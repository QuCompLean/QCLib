/-
Copyright (c) 2026 Georgios Afentakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Georgios Afentakis.
-/
module

import Lean
public meta import Lean.Elab.Tactic.Location
public meta import Lean.Elab.Tactic.Rewrite
public meta import Lean.Meta.Eqns
public meta import Lean.Meta.Tactic.Assumption

/-!

Port of Lean3 `assoc_rw` tactic.

An more modern version is currently being written in another repo.

-/

open Lean Meta Elab Tactic
namespace AssocRewrite

meta def matchFn (fn : Expr) : Expr → MetaM (Expr × Expr)
  | .app (.app fn' e₀) e₁ => do
    if ← isDefEq fn fn' then return (e₀, e₁)
    else throwError "matchFn: function mismatch"
  | _ => throwError "matchFn: not a binary application"

meta def chainEqTrans : List Expr → MetaM Expr
  | []      => throwError "chainEqTrans: empty list"
  | [e]     => pure e
  | e :: es => do
      let rest ← chainEqTrans es
      mkEqTrans e rest

meta partial def mkAssocPattern' (fn : Expr) : Expr → MetaM (List Expr)
  | e =>
    (do let (e₀, e₁) ← matchFn fn e
        let l ← mkAssocPattern' fn e₀
        let r ← mkAssocPattern' fn e₁
        return l ++ r) <|>
    pure [e]

meta def mkAssocPattern (fn e : Expr) : MetaM (List Expr) :=
  mkAssocPattern' fn e

meta def unifyPrefix : List Expr → List Expr → MetaM Unit
  | [], _ => pure ()
  | _, [] => throwError "unifyPrefix: prefix too long"
  | x :: xs, y :: ys => do
    guard (← isDefEq x y)
    unifyPrefix xs ys

-- Mimics Lean 3, maybe do it directly.
private structure RwRule where
  symm : Bool
  term : TSyntax `term

meta partial def matchAssocPattern' (p : List Expr) : List Expr → MetaM (List Expr × List Expr)
  | es => (do
      unifyPrefix p es
      return ([], es.drop p.length)) <|>
    match es with
    | []      => throwError "matchAssocPattern': no match"
    | x :: xs => Prod.map (x :: ·) id <$> matchAssocPattern' p xs
meta def mkAssocInstance (α fn : Expr) : MetaM Expr := do
  let lamFn ← withLocalDeclD `a α fun a =>
    withLocalDeclD `b α fun b => do
      mkLambdaFVars #[a, b] (mkApp (mkApp fn a) b)
  let t ← mkAppOptM ``Std.Associative #[some α, some lamFn]
  let inst ← synthInstance t
    <|> throwError "{fn} is not associative"
  mkAppOptM ``Std.Associative.assoc #[some α, some lamFn, some inst]
meta def matchAssocPattern (fn p e : Expr) : MetaM (List Expr × List Expr) := do
  let p' ← mkAssocPattern fn p
  let e' ← mkAssocPattern fn e
  matchAssocPattern' p' e'


meta partial def mkAssoc (fn : Expr) : List Expr → MetaM Expr
  | []           => throwError "mkAssoc: empty list"
  | [x]          => pure x
  | x₀ :: x₁ :: xs => mkAssoc fn (mkApp (mkApp fn x₀) x₁ :: xs)


meta partial def assocRoot (fn assoc : Expr) : Expr → MetaM (Expr × Expr)
  | e => (do
    let (e₀, e₁) ← matchFn fn e
    let (ea, eb) ← matchFn fn e₁
    let e' := mkApp (mkApp fn (mkApp (mkApp fn e₀) ea)) eb
    let p' ← mkEqSymm (mkApp (mkApp (mkApp assoc e₀) ea) eb)
    let (e'', p'') ← assocRoot fn assoc e'
    Prod.mk e'' <$> mkEqTrans p' p'') <|>
    (Prod.mk e <$> mkEqRefl e)

meta partial def assocRefl' (fn assoc : Expr) : Expr → Expr → MetaM Expr
  | l, r => (do
      guard (← isDefEq l r)
      mkEqRefl l) <|> do
-- The A B C D G H error thing is something I carried over from Lean 3. Maybe write better errors.
    let (l', l_p)   ← assocRoot fn assoc l  <|> throwError "A"
    let (el₀, el₁) ← matchFn fn l'          <|> throwError "B"
    let (r', r_p)   ← assocRoot fn assoc r  <|> throwError "C"
    let (er₀, er₁) ← matchFn fn r'          <|> throwError "D"
    let p₀   ← assocRefl' fn assoc el₀ er₀
    let p₁   ← isDefEq el₁ er₁ *> mkEqRefl el₁
    let f_eq ← mkCongrArg fn p₀             <|> throwError "G"
    let p'   ← mkCongr f_eq p₁              <|> throwError "H"
    let r_p' ← mkEqSymm r_p
    chainEqTrans [l_p, p', r_p']
meta def assocRefl (fn : Expr) : TacticM Unit := do
  let goal ← getMainGoal
  let (l, r) ← goal.withContext do
    let tgt ← goal.getType
    let some (_, l, r) ← liftMetaM <| matchEq? tgt
      | throwError "assoc_refl: goal is not an equality"
    return (l, r)
  let α ← goal.withContext <| liftMetaM <| inferType l
  let assoc ← goal.withContext <| liftMetaM <| mkAssocInstance α fn
    <|> throwError "{fn} is not associative"
  let p ← goal.withContext <| liftMetaM <| assocRefl' fn assoc l r
  goal.assign p

meta def flatten (fn assoc e : Expr) : MetaM (Expr × Expr) := do
  let ls ← mkAssocPattern fn e
  let e' ← mkAssoc fn ls
  let p  ← assocRefl' fn assoc e e'
  return (e', p)


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

/-- Enumerate all binary-application subexpressions, without committing to a
particular operator. `assocRewriteIntl` filters by operator via `matchFn`. -/
-- Maybe do it with only assoc experssions and not all binary like lean 3
-- But this fixes the pauli-comp use case. It is probably the fn filtering
meta partial def enumBinSubexpr : Expr → MetaM (List Expr)
  | e => do
    let here := if e.isApp && e.appFn!.isApp && !e.hasLooseBVars then [e] else []
    let below ← e.foldlM (fun es e' => do
      return es ++ (← enumBinSubexpr e')) []
    return here ++ below

meta def assocRewriteIntl (optAssoc : Option Expr) (h e : Expr) :
    MetaM (Expr × Expr) := do
  let h ← instantiateMVars h
  let t ← inferType h
  let some (_, lhs, _) ← matchEq? t
    | throwError "assocRewriteIntl: not an equality"
  unless lhs.isApp && lhs.appFn!.isApp do
    throwError "assocRewriteIntl: lhs is not a binary application"
  let fn ← instantiateMVars lhs.appFn!.appFn!
  let (l, r) ← matchAssocPattern fn lhs e
  let α ← inferType (← instantiateMVars lhs.appArg!)
  let assoc ← match optAssoc with
    | some a => pure a
    | none   => mkAssocInstance α fn
  let (lhs', rhs', h') ← mkEqProof fn l r h
  let e_p ← assocRefl' fn assoc e lhs'
  let (rhs'', rhs_p) ← flatten fn assoc rhs'
  let final_p ← chainEqTrans [e_p, h', rhs_p]
  return (rhs'', final_p)
meta partial def fillArgs (e : Expr) : MetaM (Expr × Array Expr) := do
  let e ← instantiateMVars e
  match e with
  | .forallE _ d b _ => do
    let v ← mkFreshExprMVar (some d)
    let (r, vs) ← fillArgs (b.instantiate1 v)
    return (r, #[v] ++ vs)
  | _ => return (e, #[])

meta def mfirst {m : Type → Type} [Monad m] [Alternative m] {α β : Type}
    (f : α → m β) : List α → m β
  | []      => failure
  | x :: xs => f x <|> mfirst f xs
meta def assocRewrite (h e : Expr) (optAssoc : Option Expr := none) (symm : Bool := false) :
    TacticM (Expr × Expr × Array Expr) := do
  let goal ← getMainGoal
  let rawType ← goal.withContext <| liftMetaM <| inferType h
  let (_, vs) ← goal.withContext <| liftMetaM <| fillArgs rawType
  let es ← goal.withContext <| liftMetaM <| enumBinSubexpr e
  let (e', p) ← goal.withContext <|
    mfirst (fun candidate => do
      let hInst ← liftMetaM <| instantiateMVars (mkAppN h vs)
      let hInst ← if symm then liftMetaM <| mkEqSymm hInst else pure hInst
      assocRewriteIntl optAssoc hInst candidate) es
  let p ← goal.withContext <| liftMetaM <| instantiateMVars p
  return (e', p, vs)

private meta def assocRewriteTarget (e : Expr) (symm : Bool) : TacticM Unit := do
  let tgt := (← (← getMainGoal).getType).consumeMData
  let (_, p, _) ← assocRewrite e tgt (symm := symm)
  let goal ← getMainGoal
  let p ← liftMetaM <| instantiateMVars p
  let r ← goal.rewrite tgt p false
  let newGoal ← goal.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (newGoal :: r.mvarIds)
private meta def getRuleEqnLemmas (e : Expr) : MetaM (Array Name) := do
  match e.getAppFn with
  | .const name _ => return (← getEqnsFor? name).getD #[]
  | _ => return #[]
private meta def assocRwGoal (rs : List RwRule) : TacticM Unit :=
  rs.forM fun r => withTacticInfoContext r.term do
    let goal ← getMainGoal
    let e ← goal.withContext do
      (Elab.Term.elabTermAndSynthesize r.term none) <|>
      (Elab.Term.elabTerm r.term none)
    let e ← goal.withContext <| liftMetaM <| instantiateMVars e
    let eqns ← goal.withContext <| liftMetaM <| getRuleEqnLemmas e
    try
      assocRewriteTarget e r.symm
    catch ex =>
      try
        mfirst (fun n => do
          let eLem ← liftMetaM <| mkConstWithFreshMVarLevels n
          assocRewriteTarget eLem r.symm) eqns.toList
      catch ex2 =>
        throwError "assoc_rw: failed to rewrite using {r.term}\nDirect error: {ex.toMessageData}\n
        Eqn error: {ex2.toMessageData}"
private meta def assocRewriteHyp (h hyp : Expr) (symm : Bool)
    (optAssoc : Option Expr := none) : TacticM Expr := do
  let (_, p, _) ← do
    let goal ← getMainGoal
    goal.withContext do
      let tgt := (← liftMetaM <| inferType hyp).consumeMData
      assocRewrite h tgt optAssoc symm
  let goal ← getMainGoal
  goal.withContext do
    let tgt := (← liftMetaM <| inferType hyp).consumeMData
    let p ← liftMetaM <| instantiateMVars p
    let r ← goal.rewrite tgt p false
    let result ← goal.replaceLocalDecl hyp.fvarId! r.eNew r.eqProof
    replaceMainGoal (result.mvarId :: r.mvarIds)
    return mkFVar result.fvarId
private meta def usesHyp (e : Expr) (h : Expr) : Bool :=
  (e.find? (· == h)).isSome


private meta def assocRwHyp : List RwRule → Expr → TacticM Unit
  | [], _ => pure ()
  | r :: rs, hyp => do
    let hyp' ← withTacticInfoContext r.term do
      let goal ← getMainGoal
      let e ← goal.withContext <| Elab.Term.elabTermAndSynthesize r.term none
      let eqns ← goal.withContext <| liftMetaM <| getRuleEqnLemmas e
      if usesHyp e hyp then pure hyp
      else
        (do assocRewriteHyp e hyp r.symm) <|>
        mfirst (fun n => do
          let eLem ← liftMetaM <| mkConstWithFreshMVarLevels n
          assocRewriteHyp eLem hyp r.symm) eqns.toList <|>
        throwError "assoc_rw: rewrite failed"
    assocRwHyp rs hyp'

private meta def assocRwCore (rules : List RwRule) (loc : Location) : TacticM Unit := do
  withLocation loc
    (atLocal  := fun fvarId => assocRwHyp rules (mkFVar fvarId))
    (atTarget := assocRwGoal rules)
    (failed   := fun _ => throwError "assoc_rw: no location succeeded")
  try evalTactic (← `(tactic| with_reducible ac_rfl)) catch _ => pure ()
--  ac_rfl does not close some cases like  (a * b * c)*d ∈ s ↔ ((c * c)*d) ∈ s
  try evalTactic (← `(tactic| with_reducible rfl)) catch _ => pure ()

/-- `assoc_rewrite [h₀, ← h₁] at ⊢ h₂` behaves like `rewrite [...]` but uses
    associativity implicitly. Works for any `Std.Associative` operator. -/
elab "assoc_rewrite" "[" rs:Lean.Parser.Tactic.rwRule,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic => do
  let loc := loc.map expandLocation |>.getD (Location.targets #[] true)
  let rules ← rs.getElems.toList.mapM fun (r : TSyntax `Lean.Parser.Tactic.rwRule) => do
   match r with
    | `(Lean.Parser.Tactic.rwRule| ← $t:term) => pure { symm := true,  term := t : RwRule }
    | `(Lean.Parser.Tactic.rwRule| $t:term)   => pure { symm := false, term := t : RwRule }
    | _ => throwError "unexpected rule syntax"
  assocRwCore rules loc
/-- Synonym for `assoc_rewrite`. -/
macro "assoc_rw" "[" rs:Lean.Parser.Tactic.rwRule,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| assoc_rewrite [$rs,*] $[$loc]?)

end AssocRewrite
