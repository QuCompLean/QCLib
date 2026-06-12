/-
Copyright (c) 2026 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross, Andrés Goens
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public meta import Mathlib.Tactic.FinCases
public meta import Mathlib.Tactic.FieldSimp
public meta import Mathlib.Tactic.Ring.RingNF
import Mathlib.LinearAlgebra.StdBasis


/-!

# Proving equality of small matrices

`matrix_expand` attempts to prove the equality between two matrices indexed by a concrete
`Fintype`. This is done by element-wise comparision.

`*_def` lemmas can be tagged by `matrixExpand` to allow automatic unfolding of
definitions in `matrix_expand`.

`matrix_neq` is a simple tactic for proving inequality of a unitary matrix an identity.


# Origin & Problems

This tactic was initially taken from `Timeroot/Lean-QuantumInfo` github repo.

The original implementation is able to prove equalities between
matrices indexed by `Fin n`. However, when applied to matrices indexed by
tuples, it fails to simplify certain expressions.

This limitation stems from the construction of the `Fintype` instance ` Pi.instFintype`
for functions of type `Fin n → Fin d`. Internally, this instance is derived from
`Multiset.pi`, which constructs dependent Fintype functions using `Pi.cons`.
This results in overly complicated terms, which often can't be handled by `simp`.

The following example illustrates the issue:

```
example (a : Fin 2 → Fin 2) : a ∈ [![0, 0], ![0, 1], ![1, 0], ![1,1]] := by
  fin_cases a
  simp -- fails to prove the goal
```

To address this, we define `piFinList`, a recursively constructed List containing all
elements of `Fin n → Fin d`. This explicit enumeration avoids the additional abstraction
introduced by the default Fintype instance and provides a representation that is
more amenable to simplification.


# TBD

Finding replacement for `matrix_neq`.

-/


@[expose] public section

open Matrix

def piFinList : (n : ℕ) → (d : ℕ) → List (Fin n → Fin d)
  | 0, _      => [vecEmpty]
  | n + 1, d  => (List.finRange d).flatMap fun a => (piFinList n d).map (vecCons a)

theorem piFinList_complete {n d} (l : Fin n → Fin d) : l ∈ piFinList n d := by
  induction n with
  | zero =>
    simp only [piFinList, List.mem_cons, List.not_mem_nil, or_false]
    ext i
    exact Fin.elim0 i
  | succ k ih =>
    simpa [piFinList] using ⟨l 0, l ∘ Fin.succ, ih (l ∘ Fin.succ ), cons_head_tail l⟩

-- Move to Mathlib for upstream?
theorem Finset.sum_vecCons {M} [AddCommMonoid M] {n m : ℕ} (f : (Fin n.succ → Fin m) → M) :
    ∑ x, f x = ∑ k, ∑ x, f (vecCons k x) := by
  let e (k) : (Fin n → Fin m) ↪ (Fin n.succ → Fin m) := ⟨fun r ↦ vecCons k r, fun _ => by simp⟩
  have hb : (univ : Finset (Fin n.succ → Fin m)) = univ.biUnion (fun k => univ.map (e k)) := by
    ext k
    simpa using ⟨k 0, Fin.tail k, (cons_head_tail k)⟩
  have hdis : Set.PairwiseDisjoint (α := Finset (Fin n.succ → Fin m)) (univ : Finset (Fin m))
    (fun k => univ.map (e k)) := by
    intro _ _ _ _ hk
    simpa [Finset.disjoint_left, e] using fun _ h => hk h.symm
  rw [hb, Finset.sum_biUnion (hdis)]
  simp [e]

-- Used in hack below.
theorem matrix_neq_of_diag_neq {n α : Type*} (U V : Matrix n n α)
    (hneq : ∃ i : n, ¬(U i i = V i i)) : ¬U = V := by
  grind

end


meta section

open Lean.Meta

namespace Lean.Elab.Tactic

/--
  Enables passing unnamed proofs directly to fin_cases.
  This is to avoid adding `piFinList_complete` into context as a named
  hypothesis and remove it later.
-/
elab_rules : tactic
  | `(tactic| fin_cases $[$hyps:term],*) => withMainContext <| focus do
    for h in hyps do
      allGoals do
        -- Try to resolve as a local fvar first (the ident case)
        let elaborated ← elabTerm h none
        if let .fvar fvarId := elaborated then
          -- It's an existing hypothesis, use direct path (original behavior)
          liftMetaTactic (finCasesAt · fvarId)
        else
          -- It's an arbitrary term, assert it as a new hypothesis
          let ty ← inferType elaborated
          liftMetaTactic fun g => do
            let (fvarId, g') ← (← g.assert `_fin_cases_tmp ty elaborated).intro1P
            finCasesAt g' fvarId


open Lean.Parser.Tactic in
/-- Proves goals equating small matrices by expanding out products and simplifying
standard Real arithmetic. Optionally accepts: `[rules]` – extra simp lemmas
-/
syntax (name := matrix_expand) "matrix_expand"
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

register_simp_attr matrixExpand

macro_rules
| `(tactic| matrix_expand $[[$rules,*]]? ) => do
  let rules' := rules.getD ⟨#[]⟩
  `(tactic|
    (set_option linter.unusedRCasesPattern false in ext i j) <;>
    -- falls back to default `Fintype` instances if the type is not `Fin n → Fin d`.
    (first | fin_cases (piFinList_complete i) | fin_cases i) <;>
    (try (first | fin_cases (piFinList_complete j) | fin_cases j))
      <;> simp [matrixExpand, Matrix.mul_apply, Matrix.one_apply, Matrix.mulVec_add,
                Matrix.mulVec_smul, Matrix.one_apply,
                Finset.sum_vecCons, Pi.single_apply,
              -- `smul_def` can take very long searching in vain for `SMul ℂ unitaryGroup`
                Submonoid.smul_def,
                Pi.basisFun_apply, Fintype.sum_prod_type,
                Subsingleton.elim _ ![],            -- eliminates dummy indices in kets
                $[$rules'],* ]
      <;> try field_simp
      <;> ring_nf
      <;> norm_cast
      <;> norm_num)


/- This is a hack for proving that a unitary isn't `1`. To be fixed. -/
/- TBD: Sensible implementation. -/

open Lean.Parser.Tactic in
syntax (name := matrix_neq) "matrix_neq"
  (" [" ((simpStar <|> simpErase <|> simpLemma),*,?) "]")? : tactic

-- `Subtype.ext_iff` reduces unitaries to matrices
-- `ne_eq` reduces `a ≠ b` to `¬a=b`
macro_rules
| `(tactic| matrix_neq $[[$rules,*]]? ) => do
  let rules' := rules.getD ⟨#[]⟩
  `(tactic|
    simp only [Subtype.ext_iff, ne_eq, $[$rules'],* ] <;>
    apply matrix_neq_of_diag_neq <;>
    simp <;>
    norm_cast
  )


end Lean.Elab.Tactic

end
