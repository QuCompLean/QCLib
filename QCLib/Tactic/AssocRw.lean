/-
Copyright (c) 2026 Georgios Afentakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Afentakis.
-/
module
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Elab.Tactic.Rewrite
public meta import Lean.Meta.Eqns
public meta import Lean.Meta.Tactic.AC.Main
open Lean Meta Elab Tactic
namespace AssocRewrite

inductive RwScheme | left | right

private structure RwRule where
  symm   : Bool
  term   : TSyntax `term
  scheme : RwScheme := .left

/-- Check that an expression is a binary application of fn and return its two arguments.--/
meta def matchFn (fn : Expr) : Expr → MetaM (Expr × Expr)
  | .app (.app fn' e₀) e₁ => do
    if ← isDefEq fn fn' then return (e₀, e₁)
    else throwError "matchFn: function mismatch"
  | _ => throwError "matchFn: not a binary application"

-- Flatten an ACExpr tree into left to right sequence of leaf indices.
meta def flatten : Lean.Data.AC.Expr → List Nat
  | .var idx => [idx]
  | .op l r  => flatten l ++ flatten r

-- Chain a list of equality proofs into a single proof by transitivity.
meta def chainEqTrans : List Expr → MetaM Expr
  | []      => throwError "chainEqTrans: empty list"
  | [e]     => pure e
  | e :: es => do
      let rest ← chainEqTrans es
      mkEqTrans e rest

-- Check that the LHS atom list matches the target
-- i.e. just a guard
meta def unifyLhs (atomsT : Array Expr) :
    List Expr → List Nat → MetaM Unit
  | [], _ => pure ()
  | _, [] => throwError "unifyLhsPrefix: pattern longer than target suffix"
  | x :: xs, j :: js => do
    guard (← isDefEq x atomsT[j]!)
    unifyLhs atomsT xs js

-- Slide the LHS along the target leaf indices until a matching position is found
-- return the indices before and after the match.
meta partial def findMatch (atomsT : Array Expr) (lhs : List Expr) :
    List Nat → MetaM (List Nat × List Nat)
  | tgt => (do
      unifyLhs atomsT lhs tgt
      return ([], tgt.drop lhs.length)) <|>
    match tgt with
    | []      => throwError "findMatch: LHS not found in target"
    | x :: xs => Prod.map (x :: ·) id <$> findMatch atomsT lhs xs
-- Return the flat atom list of an expression with respect to fn.
meta partial def mkAssocPattern (fn : Expr) : Expr → MetaM (List Expr)
  | e =>
    (do let (e₀, e₁) ← matchFn fn e
        let l ← mkAssocPattern fn e₀
        let r ← mkAssocPattern fn e₁
        return l ++ r) <|>
    pure [e]
-- Fold a list of expressions into a left-associated binary application of fn.
meta partial def mkAssoc (fn : Expr) : List Expr → MetaM Expr
  | []              => throwError "mkAssoc: empty list"
  | [x]             => pure x
  | x₀ :: x₁ :: xs => mkAssoc fn (mkApp (mkApp fn x₀) x₁ :: xs)

-- Construct a proof of e1 = e2 by calling ac_rfl on a fresh metavariable.
meta def acReflProof (e₁ e₂ : Expr) : MetaM Expr := do
  let goalType ← mkEq e₁ e₂
  let mvar ← mkFreshExprMVar (some goalType)
  Lean.Meta.AC.rewriteUnnormalizedRefl mvar.mvarId!
  instantiateMVars mvar

-- Wrap a proof of l = r with surrounding prefix and suffix expressions
meta def mkEqProof (fn : Expr) (e₀ e₁ : List Expr) (p : Expr) :
    MetaM (Expr × Expr × Expr) := do
  let t ← inferType p
  let some (_, l, r) ← matchEq? t | throwError "mkEqProof: not an equality"
  if e₀.isEmpty && e₁.isEmpty then
    return (l, r, p)
  else
    let l' ← mkAssoc fn (e₀ ++ [l] ++ e₁)
    let r' ← mkAssoc fn (e₀ ++ [r] ++ e₁)
    let t  ← inferType l'
    withLocalDecl `x .default t fun v => do
      let e  ← mkAssoc fn (e₀ ++ [v] ++ e₁)
      let p' ← mkCongrArg (← mkLambdaFVars #[v] e) p
      let p' := p'.headBeta
      return (l', r', p')
-- Collect all binary subexpressions of e, including e itself if applicable (fixing todo).
-- One could check only for assoc expressions but this breaks the pauli_comp use case (i think)
meta partial def enumBinSubexpr : Expr → MetaM (List Expr)
  | e => do
    let here := if e.isApp && e.appFn!.isApp && !e.hasLooseBVars then [e] else []
    let below ← e.foldlM (fun es e' => do
      return es ++ (← enumBinSubexpr e')) []
    return here ++ below
/-! ## Tree using ACExpr -/
-- Convert a Lean expression to an ACExpr tree, collecting atoms into the array and reusing existing ones by DEFINITIONAL equality.
meta partial def exprToAC (fn : Expr) (e : Expr)
    (atoms : Array Expr) : MetaM (Array Expr × Lean.Data.AC.Expr) := do
  if e.isApp && e.appFn!.isApp then
    if ← isDefEq fn e.appFn!.appFn! then
      let (atoms, l) ← exprToAC fn e.appFn!.appArg! atoms
      let (atoms, r) ← exprToAC fn e.appArg! atoms
      return (atoms, .op l r)
  for i in List.range atoms.size do
    if ← isDefEq atoms[i]! e then
      return (atoms, .var i)
  return (atoms.push e, .var atoms.size)

-- Walk the ACExpr tree and replace entries in the matched region with the rhs index, and marks the dummy.
meta def annotateAC (lo hi anchorIdx rhsIdx dummyIdx : Nat) :
    Lean.Data.AC.Expr → Nat → Lean.Data.AC.Expr × Nat
  | .var idx, i =>
      if i == anchorIdx then (.var rhsIdx, i + 1)
      else if lo ≤ i && i < hi then (.var dummyIdx, i + 1)
      else (.var idx, i + 1)
  | .op l r, i =>
      let (l', i₁) := annotateAC lo hi anchorIdx rhsIdx dummyIdx l i
      let (r', i₂) := annotateAC lo hi anchorIdx rhsIdx dummyIdx r i₁
      (.op l' r', i₂)
-- Remove all dummy entries from an ACExpr tree, collapsing op nodes that become empty.
meta def RemoveDummyAC (dummyIdx : Nat) : Lean.Data.AC.Expr → Option Lean.Data.AC.Expr
  | .var idx =>
      if idx == dummyIdx then none else some (.var idx)
  | .op l r =>
  -- Replace whole branches with left and right leaves by a single dummy-less expression
      match RemoveDummyAC dummyIdx l, RemoveDummyAC dummyIdx r with
      | none,    none    => none
      | none,    some r' => some r'
      | some l', none    => some l'
      | some l', some r' => some (.op l' r')
-- Convert an ACExpr tree back to a Lean expression by looking up atoms and rebuilding applications of fn.
meta partial def acToExpr (fn : Expr) (atoms : Array Expr) :
    Lean.Data.AC.Expr → MetaM Expr
  | .var idx => pure atoms[idx]!
  | .op l r => return mkApp (mkApp fn (← acToExpr fn atoms l))
                                       (← acToExpr fn atoms r)

-- Build the rewritten expression by annotating the AC tree at the matched region, pruning dummy leaves, and converting back to a Lean expression.
meta def structuredRewrite (fn e : Expr) (prefixLen lhsLeafCount : Nat)
    (ruleRhs : Expr) (scheme : RwScheme) : MetaM Expr := do
  let (atoms, acTree) ← exprToAC fn e #[]
  let dummyIdx := atoms.size
  let rhsIdx   := atoms.size + 1
  let atoms    := atoms.push ruleRhs |>.push ruleRhs  -- push same thing twice, create two things one is for dummy metamorphosis
  let min_l       := prefixLen
  let max_l        := prefixLen + lhsLeafCount
  let anchorIdx := match scheme with | .left => min_l | .right => max_l - 1
  -- replace with dummy when needed if not anchor
  let (acTree', _) := annotateAC min_l max_l anchorIdx rhsIdx dummyIdx acTree 0
  -- Remove the dummys from the tree
  match RemoveDummyAC dummyIdx acTree' with
  | some t => acToExpr fn atoms t
  | none   => pure ruleRhs

-- Find the LHS of h in e up to associativity and return the rewritten expression together with a proof of the equality.
meta def assocRewriteIntl (h e : Expr) (scheme : RwScheme := .left) :
    MetaM (Expr × Expr) := do
  let h ← instantiateMVars h
  let t ← inferType h
  let some (_, lhs, ruleRhs) ← matchEq? t
    | throwError "assocRewriteIntl: not an equality"
  unless lhs.isApp && lhs.appFn!.isApp do
    throwError "assocRewriteIntl: lhs is not a binary application"
  let fn ← instantiateMVars lhs.appFn!.appFn!
  let _ ← Lean.Meta.AC.preContext fn
    <|> throwError "assocRewriteIntl: {fn} is not associative"
  let (atomsT, acTarget) ← exprToAC fn e #[]
  let tgtLeaves := flatten acTarget
  let lhsLeaves ← mkAssocPattern fn lhs
  let (preIdx, sufIdx) ← findMatch atomsT lhsLeaves tgtLeaves
  let pre := preIdx.map (atomsT[·]!)
  let suf := sufIdx.map (atomsT[·]!)
  let (lhs', rhs', h') ← mkEqProof fn pre suf h
  let e_p ← acReflProof e lhs'
  let result ← structuredRewrite fn e pre.length lhsLeaves.length ruleRhs scheme
  let rhs_p ← acReflProof rhs' result
  let final_p ← chainEqTrans [e_p, h', rhs_p]
  return (result, final_p)
-- ## Tactic wrapping up
-- Instantiate all implicit arguments of e with fresh metavariables, returning the result and the array of new metavariables.
meta partial def fillArgs (e : Expr) : MetaM (Expr × Array Expr) := do
  let e ← instantiateMVars e
  match e with
  | .forallE _ d b _ => do
    let v ← mkFreshExprMVar (some d)
    let (r, vs) ← fillArgs (b.instantiate1 v)
    return (r, #[v] ++ vs)
  | _ => return (e, #[])
-- Try f on each element of the list in order, returning the first success.
meta def mfirst {m : Type → Type} [Monad m] [Alternative m] {α β : Type}
    (f : α → m β) : List α → m β
  | []      => failure
  | x :: xs => f x <|> mfirst f xs

-- Try to rewrite e in the expression using h, trying each binary subexpression as a candidate.
meta def assocRewrite (h e : Expr) (symm : Bool := false)
    (scheme : RwScheme := .left) : TacticM (Expr × Expr × Array Expr) := do
  let goal ← getMainGoal
  let rawType ← goal.withContext <| liftMetaM <| inferType h
  let (_, vs) ← goal.withContext <| liftMetaM <| fillArgs rawType
  let es ← goal.withContext <| liftMetaM <| enumBinSubexpr e
  let (e', p) ← goal.withContext <|
    mfirst (fun candidate => do
      let hInst ← liftMetaM <| instantiateMVars (mkAppN h vs)
      let hInst ← if symm then liftMetaM <| mkEqSymm hInst else pure hInst
      assocRewriteIntl hInst candidate scheme) es
  let p ← goal.withContext <| liftMetaM <| instantiateMVars p
  return (e', p, vs)
-- Rewrite the main goal target using e and replace the goal with the rewritten version.
private meta def assocRewriteTarget (e : Expr) (symm : Bool) (scheme : RwScheme) :
    TacticM Unit := do
  let tgt := (← (← getMainGoal).getType).consumeMData
  let (_, p, _) ← assocRewrite e tgt (symm := symm) (scheme := scheme)
  let goal ← getMainGoal
  let p ← liftMetaM <| instantiateMVars p
  let r ← goal.rewrite tgt p false
  let newGoal ← goal.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (newGoal :: r.mvarIds)
-- Look up the equation lemmas generated for a definition, returning an empty array if none exist.
private meta def getRuleEqnLemmas (e : Expr) : MetaM (Array Name) := do
  match e.getAppFn with
  | .const name _ => return (← getEqnsFor? name).getD #[]
  | _ => return #[]
-- Apply each rule in the list to the goal target, falling back to equation lemmas if the direct rewrite fails.
private meta def assocRwGoal (rs : List RwRule) : TacticM Unit :=
  rs.forM fun r => withTacticInfoContext r.term do
    let goal ← getMainGoal
    let e ← goal.withContext do
      (Elab.Term.elabTermAndSynthesize r.term none) <|>
      (Elab.Term.elabTerm r.term none)
    let e ← goal.withContext <| liftMetaM <| instantiateMVars e
    let eqns ← goal.withContext <| liftMetaM <| getRuleEqnLemmas e
    try
      assocRewriteTarget e r.symm r.scheme
    catch ex =>
      try
        mfirst (fun n => do
          let eLem ← liftMetaM <| mkConstWithFreshMVarLevels n
          assocRewriteTarget eLem r.symm r.scheme) eqns.toList
      catch ex2 =>
        throwError "assoc_rw: failed to rewrite using {r.term}\nDirect: {ex.toMessageData}\nEqn: {ex2.toMessageData}"
-- Rewrite the type of a hypothesis using h and return the new hypothesis expression.
private meta def assocRewriteHyp (h hyp : Expr) (symm : Bool) (scheme : RwScheme) :
    TacticM Expr := do
  let (_, p, _) ← do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := (← liftMetaM <| inferType hyp).consumeMData
      assocRewrite h tgt symm scheme
  let goal ← getMainGoal
  goal.withContext do
    let tgt := (← liftMetaM <| inferType hyp).consumeMData
    let p ← liftMetaM <| instantiateMVars p
    let r ← goal.rewrite tgt p false
    let result ← goal.replaceLocalDecl hyp.fvarId! r.eNew r.eqProof
    replaceMainGoal (result.mvarId :: r.mvarIds)
    return mkFVar result.fvarId
-- Check whether h appears anywhere inside e.
private meta def usesHyp (e : Expr) (h : Expr) : Bool :=
  (e.find? (· == h)).isSome
-- Apply each rule in the list to a hypothesis in sequence, passing the updated hypothesis forward.
private meta def assocRwHyp : List RwRule → Expr → TacticM Unit
  | [], _ => pure ()
  | r :: rs, hyp => do
    let hyp' ← withTacticInfoContext r.term do
      let goal ← getMainGoal
      let e ← goal.withContext <| Elab.Term.elabTermAndSynthesize r.term none
      let eqns ← goal.withContext <| liftMetaM <| getRuleEqnLemmas e
      if usesHyp e hyp then pure hyp
      else
        (do assocRewriteHyp e hyp r.symm r.scheme) <|>
        mfirst (fun n => do
          let eLem ← liftMetaM <| mkConstWithFreshMVarLevels n
          assocRewriteHyp eLem hyp r.symm r.scheme) eqns.toList <|>
        throwError "assoc_rw: rewrite failed"
    assocRwHyp rs hyp'
-- Dispatch the list of rules to hypotheses or the goal depending on the given location.
private meta def assocRwCore (rules : List RwRule) (loc : Location) : TacticM Unit := do
  withLocation loc
    (fun fvarId => assocRwHyp rules (mkFVar fvarId))
    (assocRwGoal rules)
    (fun _ => throwError "assoc_rw: no location succeeded")

/-! ## Syntax -/

elab "assoc_rewrite" "[" rs:Lean.Parser.Tactic.rwRule,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => do
  let loc := loc.map expandLocation |>.getD (Location.targets #[] true)
  let rules ← rs.getElems.toList.mapM fun (r : TSyntax `Lean.Parser.Tactic.rwRule) => do
    match r with
    | `(Lean.Parser.Tactic.rwRule| ← $t:term) =>
        pure { symm := true,  term := t, scheme := RwScheme.left : RwRule }
    | `(Lean.Parser.Tactic.rwRule| $t:term)   =>
        pure { symm := false, term := t, scheme := RwScheme.left : RwRule }
    | _ => throwError "unexpected rule syntax"
  assocRwCore rules loc

elab "assoc_rewrite_right" "[" rs:Lean.Parser.Tactic.rwRule,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => do
  let loc := loc.map expandLocation |>.getD (Location.targets #[] true)
  let rules ← rs.getElems.toList.mapM fun (r : TSyntax `Lean.Parser.Tactic.rwRule) => do
    match r with
    | `(Lean.Parser.Tactic.rwRule| ← $t:term) =>
        pure { symm := true,  term := t, scheme := RwScheme.right : RwRule }
    | `(Lean.Parser.Tactic.rwRule| $t:term)   =>
        pure { symm := false, term := t, scheme := RwScheme.right : RwRule }
    | _ => throwError "unexpected rule syntax"
  assocRwCore rules loc

elab "assoc_rw" "[" rs:Lean.Parser.Tactic.rwRule,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => do
  let loc := loc.map expandLocation |>.getD (Location.targets #[] true)
  let rules ← rs.getElems.toList.mapM fun (r : TSyntax `Lean.Parser.Tactic.rwRule) => do
    match r with
    | `(Lean.Parser.Tactic.rwRule| ← $t:term) =>
        pure { symm := true,  term := t, scheme := RwScheme.left : RwRule }
    | `(Lean.Parser.Tactic.rwRule| $t:term)   =>
        pure { symm := false, term := t, scheme := RwScheme.left : RwRule }
    | _ => throwError "unexpected rule syntax"
  assocRwCore rules loc
  try evalTactic (← `(tactic| with_reducible ac_rfl)) catch _ => pure ()
  try evalTactic (← `(tactic| with_reducible rfl))    catch _ => pure ()
-- Maybe there is a case to use only ac_nf as closing here ↑
elab "assoc_rw_right" "[" rs:Lean.Parser.Tactic.rwRule,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => do
  let loc := loc.map expandLocation |>.getD (Location.targets #[] true)
  let rules ← rs.getElems.toList.mapM fun (r : TSyntax `Lean.Parser.Tactic.rwRule) => do
    match r with
    | `(Lean.Parser.Tactic.rwRule| ← $t:term) =>
        pure { symm := true,  term := t, scheme := RwScheme.right : RwRule }
    | `(Lean.Parser.Tactic.rwRule| $t:term)   =>
        pure { symm := false, term := t, scheme := RwScheme.right : RwRule }
    | _ => throwError "unexpected rule syntax"
  assocRwCore rules loc
  try evalTactic (← `(tactic| with_reducible ac_rfl)) catch _ => pure ()
  try evalTactic (← `(tactic| with_reducible rfl))    catch _ => pure ()
end AssocRewrite
