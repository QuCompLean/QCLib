/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import QCLib.Mathlib.LinearAlgebra.PiOuterProduct

/-!

Various ways of splitting up a `PiOuterProduct` into binary tensor products.

-/

@[expose] public section

namespace Matrix

open scoped PiOuterProduct

variable {ι : Type*} [Fintype ι]

variable {R S α α' β β' γ γ' : Type*}
variable {l m n p : Type*} {q r : Type*} {l' m' n' p' : Type*}

open Equiv

-- TBD: Version for sets?
def piTensorProductSubtypeEquiv (p : ι → Prop) [DecidablePred p] :
    ((ι → l) → α) ≃ (({i // p i} → l) × ({i // ¬p i} → l) → α) :=
    arrowCongr (piEquivPiSubtypeProd p (fun _ ↦ l)) (Equiv.refl α)

@[simp]
theorem piTensorProductSubtypeEquiv_apply (p : ι → Prop) [DecidablePred p] [CommMonoid α]
    (v : ι → l → α) (f : {i // p i} → l) (g : {i // ¬p i} → l) :
    piTensorProductSubtypeEquiv p (⨂ i, v i) (f, g) =
      (⨂ i : {i // p i}, v ↑i) f * (⨂ i : {i // ¬p i}, v ↑i) g := by
  simp [piTensorProductSubtypeEquiv, ← Fintype.prod_subtype_mul_prod_subtype (p := p)]
  congr <;> grind

def piTensorProductSplitAtEquiv (i : ι) [DecidableEq ι] :
    ((ι → l) → α) ≃ (l × ({ j // j ≠ i } → l) → α) :=
    arrowCongr (funSplitAt i l) (Equiv.refl α)

@[simp]
theorem piTensorProductSplitAtEquiv_apply [CommMonoid α] [DecidableEq ι]
    (v : ι → l → α) (i : ι) (x : l) (f : {j : ι // ¬j = i} → l) :
    piTensorProductSplitAtEquiv i (⨂ i, v i) (x, f) = v i x * (⨂ j : {j : ι // ¬j = i}, v ↑j) f
    := by
  simp [piTensorProductSplitAtEquiv, Fintype.prod_eq_mul_prod_subtype_ne (a := i)]
  congr
  grind

@[simps]
def piSplitTwo {β : ι → Type*} [DecidableEq ι] (i j : ι) (hji : j ≠ i := by grind) :
    (∀ k : ι, β k) ≃ (β i × β j) × (∀ k : {k // k ≠ i ∧ k ≠ j}, β k) where
  toFun f := ((f i, f j), fun ⟨k, hi, hj⟩ => f k)
  invFun := fun ((a, b), g) k =>
    if hki : k = i then hki.symm ▸ a
    else if hkj : k = j then hkj.symm ▸ b
    else g ⟨k, hki, hkj⟩
  left_inv := by intro _; grind
  right_inv := by intro _; aesop

omit [Fintype ι] in
@[simp]
lemma flatten_ind'_dep {k : ι → Type*}
    (i j : ι) (a b : ∀ x, k x) :
    ((a i = b i ∧ a j = b j) ∧
      ∀ x : ι, x ≠ i → x ≠ j → a x = b x) ↔
    a = b := by
  refine ⟨fun h => ?_, fun h => by simp_all⟩
  ext k
  by_cases hi : k = i <;> by_cases hj : k = j <;> grind

/- Should be relocated -/
@[simps]
def funSplitTwo [DecidableEq ι] (i j : ι) (_ : j ≠ i := by decide) :
    (ι → l) ≃ (l × l) × ({k // k ≠ i ∧ k ≠ j} → l) where
  toFun f := ((f i, f j), fun ⟨k, hi, hj⟩ => f k)
  invFun := fun ((a, b), g) k =>
    if hi : k = i then a
    else if hj : k = j then b
    else g ⟨k, hi, hj⟩
  left_inv := by intro _; grind
  right_inv := by intro _; aesop

omit [Fintype ι] in
/-- `Equiv.finSplitAt` helper. -/
@[simp]
lemma flatten_ind {k} (i) (a b : ι → k) :
    a i = b i ∧ ((fun j : { j // ¬j = i } ↦ a j) = fun j : { j // ¬j = i } ↦ b j) ↔ a = b := by
  simp [funext_iff]
  grind

omit [Fintype ι] in
@[simp]
lemma flatten_ind' {k} (i j) (a b : ι → k) :
    ((a i = b i ∧ a j = b j) ∧ ∀ (x : ι), ¬x = i → ¬x = j → a x = b x) ↔ a = b := by
  refine ⟨fun h => ?_, fun h => by simp_all⟩
  ext k
  by_cases hi : k = i
  · simp_all
  · by_cases hj : k = j
    · simp_all
    · simp_all

def piTensorProductSplitTwo [DecidableEq ι] (i j : ι) (h : j ≠ i := by decide) :
    ((ι → l) → α) ≃ ((l × l) × ({k // k ≠ i ∧ k ≠ j} → l) → α) :=
  arrowCongr (funSplitTwo i j h) (Equiv.refl α)

@[simp]
theorem piTensorProductSplitTwo_apply [CommMonoid α] [DecidableEq ι] (v : ι → l → α)
    (i j : ι) (x y : l) (f : {k : ι // k ≠ i ∧ k ≠ j} → l) (h : j ≠ i := by decide) :
    piTensorProductSplitTwo i j h (⨂ i, v i) ((x, y), f) =
      v i x * v j y * (⨂ k : {k : ι // k ≠ i ∧ k ≠ j}, v k) f := by
  simp only [ne_eq, piTensorProductSplitTwo, arrowCongr_apply, coe_refl, Function.comp_apply,
    piOuterProduct_apply, funSplitTwo_symm_apply, Fintype.prod_eq_mul_prod_subtype_ne (a := i),
    ↓reduceDIte, Fintype.prod_eq_mul_prod_subtype_ne (α := { k // ¬k = i }) (a := ⟨j, h⟩),
    dite_eq_ite, ← mul_assoc, id_eq]
  congr 1
  · grind
  · rw [Fintype.prod_equiv
      ((subtypeEquivRight (fun (x : {k // k ≠ i}) => by simp [Subtype.ext_iff])).trans
        (subtypeSubtypeEquivSubtypeInter (· ≠ i) (· ≠ j)))
      (fun (a : { i₂ // i₂ ≠ ⟨j, h⟩ }) =>
        v a (if _ : a = i then x else if _ : a = j then y else f ⟨a, by simp_all⟩))
      (fun (b : { k // k ≠ i ∧ k ≠ j }) => v b (f b))
      (by simp [subtypeEquivRight, subtypeSubtypeEquivSubtypeInter]; grind)]

omit [Fintype ι]

@[simp]
theorem piTensorProductSplitTwo_symm_apply [DecidableEq ι] (i j : ι)
    (g : (l × l) × ({k : ι // k ≠ i ∧ k ≠ j} → l) → α) (f : ι → l) (h : j ≠ i := by decide) :
    (piTensorProductSplitTwo i j h).symm g f = g ((f i, f j), fun ⟨k, _, _⟩ => f k) := by
  simp [piTensorProductSplitTwo]

end Matrix
