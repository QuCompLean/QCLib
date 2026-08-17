/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!

Various equivalences. mainly used for splitting up index types into products.

-/

@[expose] public section


variable {ι α β l : Type*}

namespace Equiv

-- Remove it (it is for matrices)
/-- `EuclideanSpace 𝕜 α` splits as the binary product of the `i`-th coordinate and the
`EuclideanSpace` on the remaining indices. -/
@[simps!]
noncomputable def EuclideanSpace.splitAt
    {α : Type*} [Fintype α] [DecidableEq α] (i : α) (𝕜 : Type*) [RCLike 𝕜] :
    EuclideanSpace 𝕜 α ≃ 𝕜 × EuclideanSpace 𝕜 { j // j ≠ i } :=
  (EuclideanSpace.equiv α 𝕜).toEquiv.trans <|
    (funSplitAt i 𝕜).trans <|
      (Equiv.refl 𝕜).prodCongr (EuclideanSpace.equiv { j // j ≠ i } 𝕜).symm

@[simps! apply symm_apply]
noncomputable def EuclideanSpace.piSplitAt
    {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) {k : ι → Type*} [∀ j, Fintype (k j)] :
    EuclideanSpace 𝕜 (k i × ((a : { j // j ≠ i }) → k ↑a)) ≃L[𝕜]
      EuclideanSpace 𝕜 ((j : ι) → k j) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 (Equiv.piSplitAt i k).symm).toContinuousLinearEquiv

-- TBD: Version stated for sets?
-- TBD: Make dependent?
-- not used.
@[simps!]
def piSplitPred (p : ι → Prop) [DecidablePred p] :
    ((ι → l) → α) ≃ (({i // p i} → l) × ({i // ¬p i} → l) → α) :=
    arrowCongr (piEquivPiSubtypeProd p (fun _ ↦ l)) (Equiv.refl α)

-- C.f. `Equiv.piSplitAt`
@[simps symm_apply]
def piSplitAtPair {β : ι → Type*} [DecidableEq ι] (i j : ι) (hji : j ≠ i := by grind) :
    (∀ k : ι, β k) ≃ (β i × β j) × (∀ k : {k // k ≠ i ∧ k ≠ j}, β k) where
  toFun f := ((f i, f j), fun ⟨k, hi, hj⟩ => f k)
  invFun := fun ((a, b), g) k =>
    if hki : k = i then hki.symm ▸ a
    else if hkj : k = j then hkj.symm ▸ b
    else g ⟨k, hki, hkj⟩
  left_inv := by intro _; grind
  right_inv := by intro _; aesop

@[simp]
theorem piSplitAtPair_applys {ι : Type u_1} {β : ι → Type u_5} [DecidableEq ι] (i j : ι)
  (hji : j ≠ i := by grind) (f : (k : ι) → β k) :
  (piSplitAtPair i j hji) f =
      ((f i, f j), fun x : {k // k ≠ i ∧ k ≠ j} => f x.1) := by
  simp [piSplitAtPair, funext_iff]

@[simps! apply symm_apply]
noncomputable def EuclideanSpace.piSplitAtPair
    {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i j : ι) {k : ι → Type*} [∀ l, Fintype (k l)] (hji : j ≠ i := by grind) :
    EuclideanSpace 𝕜 ((k i × k j) × ((a : {l // l ≠ i ∧ l ≠ j}) → k a)) ≃L[𝕜]
      EuclideanSpace 𝕜 ((l : ι) → k l) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜
    (Equiv.piSplitAtPair i j hji).symm).toContinuousLinearEquiv

-- @[simp]
-- theorem EuclideanSpace.split_funext_iff {k : ι → Type*} (i : ι) (x y : Π x, k x) :
--   ((fun j : { j // ¬j = i } ↦ x ↑j) = fun j : { j // ¬j = i } ↦ y ↑j) ∧ x i = y i ↔ x = y := by
--   simp [funext_iff]
--   grind
/-- Two functions `a b` are equal iff `(a i = b i ∧ a j = b j)` and for all
arguments `x ≠ i, j` we have `a x = b x`. Useful for case analysis. -/
@[simp]
theorem splitPair_funext_iff {k : ι → Type*} (i j : ι) (a b : Π x, k x) :
    ((a i = b i ∧ a j = b j) ∧ ∀ x : ι, x ≠ i → x ≠ j → a x = b x) ↔ a = b := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp_all⟩
  ext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> grind

@[simps apply symm_apply]
def finLEEquiv {n m} (h : n ≤ m) : Fin n ≃ {j : Fin m // j.val < n} where
  toFun i := ⟨i.castLE h, i.isLt⟩
  invFun j := ⟨j.val, j.prop⟩
  left_inv i := by simp
  right_inv j := by simp

@[simps! apply symm_apply]
def finFunSubtypeEquiv {n m} (k) [Fintype k] (h : n ≤ m) :
    (Fin n → k) ≃ ({ j : Fin m // j < n } → k) :=
  Equiv.piCongrLeft' _ (finLEEquiv h)

@[simps!]
def Fin.consFunEquiv (n k) := (Equiv.prodComm _ _).trans (Fin.consEquiv (fun _ : Fin (n + 1) => k))

-- move to LinearAlgebra.UnitaryGroup.Permutation?
section arrowCongr

/-- Version of `Equiv.arrowCongr_trans` with trivial second permutation. -/
theorem arrowCongrLeft_trans {α₁ α₂ α₃ β : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : α₂ ≃ α₃) :
    arrowCongr (e₁.trans e₂) (Equiv.refl β)
      = (arrowCongr e₁ (Equiv.refl β)).trans (arrowCongr e₂ (Equiv.refl β)) := rfl

end arrowCongr


end Equiv
