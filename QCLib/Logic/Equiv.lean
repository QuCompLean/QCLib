/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.Data.Prod.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Data.Fintype.Basic

/-!

Various equivalences. mainly used for splitting up index types into products.

-/

@[expose] public section


variable {ι α β l : Type*}

namespace Equiv

-- TBD: Version stated for sets?
-- TBD: Make dependent?
-- not used.
@[simps!]
def piSplitPred (p : ι → Prop) [DecidablePred p] :
    ((ι → l) → α) ≃ (({i // p i} → l) × ({i // ¬p i} → l) → α) :=
    arrowCongr (piEquivPiSubtypeProd p (fun _ ↦ l)) (Equiv.refl α)

-- C.f. `Equiv.piSplitAt`
@[simps]
def piSplitAtPair {β : ι → Type*} [DecidableEq ι] (i j : ι) (hji : j ≠ i := by grind) :
    (∀ k : ι, β k) ≃ (β i × β j) × (∀ k : {k // k ≠ i ∧ k ≠ j}, β k) where
  toFun f := ((f i, f j), fun ⟨k, hi, hj⟩ => f k)
  invFun := fun ((a, b), g) k =>
    if hki : k = i then hki.symm ▸ a
    else if hkj : k = j then hkj.symm ▸ b
    else g ⟨k, hki, hkj⟩
  left_inv := by intro _; grind
  right_inv := by intro _; aesop

/-- Two functions `a b` are equal iff `(a i = b i ∧ a j = b j)` and for all
arguments `x ≠ i, j` we have `a x = b x`. Useful for case analysis. -/
@[simp]
theorem splitPair_funext_iff {k : ι → Type*} (i j : ι) (a b : Π x, k x) :
    ((a i = b i ∧ a j = b j) ∧ ∀ x : ι, x ≠ i → x ≠ j → a x = b x) ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp_all⟩
  ext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> grind


-- -- Non-dep version of `piSplitTwo`? Needed?
-- @[simps]
-- def funSplitTwo [DecidableEq ι] (i j : ι) (_ : j ≠ i := by decide) :
--     (ι → l) ≃ (l × l) × ({k // k ≠ i ∧ k ≠ j} → l) where
--   toFun f := ((f i, f j), fun ⟨k, hi, hj⟩ => f k)
--   invFun := fun ((a, b), g) k =>
--     if hi : k = i then a
--     else if hj : k = j then b
--     else g ⟨k, hi, hj⟩
--   left_inv := by intro _; grind
--   right_inv := by intro _; aesop

-- /-- `Equiv.finSplitAt` helper. -/
-- @[simp]
-- lemma flatten_ind {k} (i) (a b : ι → k) :
--     a i = b i ∧ ((fun j : { j // ¬j = i } ↦ a j) = fun j : { j // ¬j = i } ↦ b j) ↔ a = b := by
--   simp [funext_iff]
--   grind
--
-- @[simp]
-- lemma flatten_ind' {k} (i j) (a b : ι → k) :
--     ((a i = b i ∧ a j = b j) ∧ ∀ (x : ι), ¬x = i → ¬x = j → a x = b x) ↔ a = b := by
--   refine ⟨fun h => ?_, fun h => by simp_all⟩
--   ext k
--   by_cases hi : k = i
--   · simp_all
--   · by_cases hj : k = j
--     · simp_all
--     · simp_all

-- -- What does this do?
-- def piTensorProductSplitTwo [DecidableEq ι] (i j : ι) (h : j ≠ i := by decide) :
--     ((ι → l) → α) ≃ ((l × l) × ({k // k ≠ i ∧ k ≠ j} → l) → α) :=
--   arrowCongr (funSplitTwo i j h) (Equiv.refl α)
--
--
-- @[simp]
-- theorem piTensorProductSplitTwo_symm_apply [DecidableEq ι] (i j : ι)
--     (g : (l × l) × ({k : ι // k ≠ i ∧ k ≠ j} → l) → α) (f : ι → l) (h : j ≠ i := by decide) :
--     (piTensorProductSplitTwo i j h).symm g f = g ((f i, f j), fun ⟨k, _, _⟩ => f k) := by
--   simp [piTensorProductSplitTwo]

-- move to LinearAlgebra.UnitaryGroup.Permutation?
section arrowCongr

/-- Version of `Equiv.arrowCongr_trans` with trivial second permutation. -/
theorem arrowCongrLeft_trans {α₁ α₂ α₃ β : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : α₂ ≃ α₃) :
    arrowCongr (e₁.trans e₂) (Equiv.refl β)
      = (arrowCongr e₁ (Equiv.refl β)).trans (arrowCongr e₂ (Equiv.refl β)) := rfl

end arrowCongr


end Equiv
