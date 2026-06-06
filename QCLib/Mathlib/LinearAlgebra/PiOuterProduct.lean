/-
Copyright (c) 2026 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Outer product of indexed families of functions and matrices

For now, put all results in one file under the `Matrix` directory, as the main
results are on Kronecker products of matrices.

## Main defintions

* `PiOuterProduct`: Tensor product of an indexed family of functions
* `PiKronecker`: Kronecker product of an indexed family of matrices
* `PiOuterProduct.toMultilinearMap` / `PiKroneckerProduct.toMultilinearMap`:
  Outer products as multilinear maps.

## Notation

* `⨂` Notation typeclass of outer products. We define instances for
  `PiOuterProduct` and `PiKronecker`.

## Main results

* `PiKronecker_det_dep` The determinant of a KroneckerProducgt

## Maturity

Fairly stable, but needs more results. Exception is the section on determinants,
which needs golfing.
-/

public section

/- Misc lemmas. Put somewhere appropriate.  -/
section Lemmas

namespace Function

/-- Consider a family `(f : ∀ a, β a → γ)` of functions with dependent domain
but non-dependent co-domain, and a family `r : ∀ a, β a` of arguments. Updating
`f` and applying at `a (r a)` is the same as updating the non-dependent function
`a ↦ f a (r a)` and applying at `a`. -/
theorem update_apply_eq_update {α γ : Type*} [DecidableEq α] {β : α → Type*} (f : ∀ a, β a → γ)
    (a' : α) (b : β a' → γ) (a : α) (r : ∀ a, β a) :
    update f a' b a (r a) = update (fun a ↦ f a (r a)) a' (b (r a')) a := by
  simp only [update_apply]
  aesop

/-- Bivariate version of `update_apply_eq_update`. -/
theorem update_apply_eq_update₂ {α γ : Type*} [DecidableEq α] {l m : α → Type*}
    (f : ∀ a, (l a) → (m a) → γ) (a' : α) (b : (l a') → (m a') → γ) (a : α) (r : ∀ a, l a)
    (s : ∀ a, m a) :
    update f a' b a (r a) (s a) = update (fun a ↦ f a (r a) (s a)) a' (b (r a') (s a')) a := by
  simp [update_apply]
  aesop

end Lemmas.Function

/-- Notation typeclass for `⨂`. We'll use the spelling `OuterProduct` for
functions / vectors and `KroneckerProduct` for matrices. -/
class PiOuterProduct {ι : Type*} (α : ι → Type*) (β : outParam (Type*)) where
  /-- The outer product of a family of objects -/
  tprod : (Π i, α i) → β

@[inherit_doc PiOuterProduct]
scoped[PiOuterProduct] notation3:100 "⨂ "(...)", "r:(scoped f => PiOuterProduct.tprod f) => r

open scoped PiOuterProduct

variable {ι : Type*} [Fintype ι] {l m n : ι → Type*} {α : Type*}

/-
# Outer product of vectors
-/

section PiOuterProductMap

variable (f : α → α → α) [LeftCommutative f]
variable (init : α)

variable {l m : ι → Type*}

/-- Given a family `v i : l i → α` of functions, produce a function defined on
tuples `r : (Π i, l i)`, where the value at `r` is obtained by folding a
function `f` over `i ↦ v i (r i) `. The usual tensor product of functions is a
special case, defined in `PiOuterProduct`. -/
def PiOuterProductMap (v : Π i, l i → α) : (Π i, l i) → α :=
  fun r ↦ (Finset.univ.1.map (fun i ↦ v i (r i))).foldr f init

@[simp]
theorem piOuterProductMap_apply (v : Π i, l i → α) (r : Π i, l i) :
  PiOuterProductMap f init v r = (Finset.univ.1.map (fun i ↦ v i (r i))).foldr f init := by rfl

end PiOuterProductMap

section PiOuterProduct

/-- Tensor product of a family of vectors -/
instance [CommMonoid α] : PiOuterProduct (fun i ↦ (l i → α)) ((Π i, l i) → α) where
  tprod := PiOuterProductMap (· * · : α → α → α) 1

theorem piOuterProduct_def [CommMonoid α] (v : Π i, (l i → α)) :
    (⨂ i, v i) = PiOuterProductMap (· * · : α → α → α) 1 v := rfl

@[simp]
theorem piOuterProduct_apply [CommMonoid α] (v : Π i, (l i → α)) (r : Π i, l i) :
    (⨂ i, v i) r =  ∏ i, v i (r i) := by
  simp [piOuterProduct_def, ← Multiset.prod_eq_foldr]

@[simp]
theorem piOuterProduct_zero [CommMonoidWithZero α] (v : Π i, (l i → α)) (h : ∃ i, v i = 0) :
    (⨂ i, v i) = 0 := by
  ext r
  obtain ⟨i, hi⟩ := h
  exact Finset.prod_eq_zero (Finset.mem_univ i) (congrFun hi (r i))

variable [CommSemiring α]

open Function in
@[simp]
theorem piOuterProduct_smul [DecidableEq ι] (v : Π i, (l i → α)) (i : ι) (s : α) (x : l i → α) :
    (⨂ j, (update v i (s • x)) j) = s • (⨂ j, (update v i x) j) := by
  ext
  simp [Function.update_apply_eq_update, Finset.prod_update_of_mem, mul_assoc]

open Function in
@[simp]
theorem piOuterProduct_add [DecidableEq ι] (v : Π i, (l i → α)) (i : ι) (x y : l i → α) :
    (⨂ j, (update v i (x + y) j)) = (⨂ j, (update v i x) j) + (⨂ j, (update v i y) j) := by
  ext
  simp [Function.update_apply_eq_update, Finset.prod_update_of_mem, add_mul]

def PiOuterProduct.toMultilinearMap :
    MultilinearMap α (fun i ↦ l i → α) ((Π i, l i) → α) where
  toFun := fun v ↦ ⨂ i, v i
  map_update_smul' := piOuterProduct_smul
  map_update_add' := piOuterProduct_add

@[simp]
theorem piOuterProduct.toMultilinearMap_apply (v : Π i, (l i → α)) :
  PiOuterProduct.toMultilinearMap v = ⨂ i, v i := by rfl

theorem piOuterProduct_smul_univ (c : ι → α) (v : Π i, (l i → α)) :
    (⨂ i, c i • v i) = (∏ i, c i) • (⨂ i, v i) := by
  simp [← piOuterProduct.toMultilinearMap_apply, MultilinearMap.map_smul_univ]

theorem piOuterProduct_smul_const (a : α) (v : Π i, (l i → α)) :
    (⨂ i, a • v i) = a^(Fintype.card ι) • (⨂ i, v i) := by
  simp [piOuterProduct_smul_univ]

theorem piOuterProduct_univ_sum [DecidableEq ι] {κ : Type*} [Fintype κ]
    (f : (i : ι) → κ → (l i) → α) : (⨂ i, ∑ j : κ , f i j) = ∑ k : (ι → κ), ⨂ i, f i (k i) := by
  ext x
  simp [Fintype.prod_sum]

end PiOuterProduct

/-
# Tensor product of matrices
-/

namespace Matrix

section PiKroneckerMap

variable (f : α → α → α) [LeftCommutative f]
variable (init : α)

/-- Given a family `A i (r i) (s i)` of matrices, produce a matrix indexed by
tuples `r : (Π i, l i)` and `s : (Π i, m i)`, where the element at `r`, `s` is
obtained by folding a function `f` over `i ↦ A i (r i) (s i)`. -/
def PiKroneckerMap (A : Π i, Matrix (l i) (m i) α) : Matrix (Π i, l i) (Π i, m i) α :=
  of fun r s ↦ (Finset.univ.1.map (fun i ↦ A i (r i) (s i))).foldr f init

@[simp]
theorem piKroneckerMap_apply (A : Π i, Matrix (l i) (m i) α) (r : Π i, l i) (s : Π i, m i) :
    PiKroneckerMap f init A r s = (Finset.univ.1.map (fun i ↦ A i (r i) (s i))).foldr f init := by
  rfl

-- Note: The binary theory is developed first for general `f`, then specialized to `*`.
-- For now, we directly start with the theory for `*`.

end PiKroneckerMap

section Kronecker

open Matrix

/-- Kronecker product of a family of matrices -/
def PiKronecker [CommMonoid α] : (A : Π i, Matrix (l i) (m i) α) → Matrix (Π i, l i) (Π i, m i) α :=
    PiKroneckerMap (· * · ) 1

instance [CommMonoid α] :
    PiOuterProduct (fun i ↦ Matrix (l i) (m i) α) (Matrix (Π i, l i) (Π i, m i) α) where
  tprod := PiKronecker

theorem piKron_matrix_def [CommMonoid α] (A : Π i, Matrix (l i) (m i) α) :
    (⨂ i, A i) = PiKronecker A := rfl

@[simp]
theorem piKronecker_apply [CommMonoid α] (A : Π i, Matrix (l i) (m i) α)
    (r : Π i, l i) (s : Π i, m i) : (⨂ i, A i) r s =  ∏ i, (A i (r i) (s i)) := by
  simp [piKron_matrix_def, PiKronecker, ← Multiset.prod_eq_foldr]

theorem piKronecker_diagonal [CommMonoidWithZero α] [∀ i, DecidableEq (m i)] (a : Π i, (m i) → α) :
    (⨂ i, diagonal (a i)) = diagonal fun rs ↦ ∏ i, (a i (rs i)) := by
  ext k l
  by_cases h : k = l
  · simp [h]
  · obtain ⟨i, hi⟩ : ∃ i, k i ≠ l i := by grind
    simpa [h] using Finset.prod_eq_zero (Finset.mem_univ i) (diagonal_apply_ne (a i) hi)

@[simp]
theorem piKronecker_one [CommMonoidWithZero α] [∀ i, DecidableEq (m i)] :
    (⨂ i, (1 : Matrix (m i) (m i) α)) = (1 : Matrix (Π i, m i) (Π i, m i) α) :=
    (piKronecker_diagonal (fun i j ↦ 1)).trans <| by simp [diagonal_one]

@[simp]
theorem piKronecker_zero [CommMonoidWithZero α] (A : Π i, Matrix (l i) (m i) α) (h : ∃ i, A i = 0) :
    (⨂ i, A i) = 0 := by
  ext
  obtain ⟨i, hi⟩ := h
  simpa using Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem mul_piKronecker_mul [CommSemiring α] [∀ i, Fintype (m i)] [DecidableEq ι]
    (A : Π i, Matrix (l i) (m i) α) (B : Π i, Matrix (m i) (n i) α) :
    (⨂ i, A i) * (⨂ i, B i) = ⨂ i, (A i) * (B i) := by
  ext
  simp only [mul_apply, piKronecker_apply, Fintype.prod_sum, Finset.prod_mul_distrib]

/-- The product of a list of simple tensors is the simple tensor with `i`-th factor equal to
the product of the `i`th factors. This generalizes `mul_piKronecker_mul`. -/
theorem _root_.List.prod_piKronecker [CommSemiring α] [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
    [DecidableEq ι] (L : List (Π i, Matrix (m i) (m i) α)) :
    (L.map (fun A ↦ ⨂ i, A i)).prod = ⨂ i, (L.map (Function.eval i)).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp_rw [List.map_cons, List.prod_cons, ← mul_piKronecker_mul]
    with_reducible congr

-- Option seems to be needed to treat `Matrix` as a function. TBD.
set_option backward.isDefEq.respectTransparency false in
open Function in
@[simp]
theorem PiKronecker_smul [CommSemiring α] [DecidableEq ι] (A : Π i, Matrix (l i) (m i) α)
    (i : ι) (s : α) (x : Matrix (l i) (m i) α) :
    (⨂ j, update A i (s • x) j) = s • ⨂ j, update A i x j := by
  ext
  simp [update_apply_eq_update₂, Finset.prod_update_of_mem, mul_assoc]

-- Option seems to be needed to treat `Matrix` as a function. TBD.
set_option backward.isDefEq.respectTransparency false in
open Function in
@[simp]
theorem PiKronecker_add [CommSemiring α] [DecidableEq ι] (A : Π i, Matrix (l i) (m i) α)
    (i : ι) (x : Matrix (l i) (m i) α) (y : Matrix (l i) (m i) α) :
    (⨂ j, update A i (x + y) j) = (⨂ j, update A i x j) + (⨂ j, update A i y j) := by
  ext k l
  simp [update_apply_eq_update₂, Finset.prod_update_of_mem, add_mul]

@[simps, expose]
def toMultilinearMap [CommSemiring α] : MultilinearMap α (fun i ↦ Matrix (l i) (m i) α)
    (Matrix (Π i, l i) (Π i, m i) α) where
  toFun f := ⨂ i, f i
  map_update_smul' := PiKronecker_smul
  map_update_add' := PiKronecker_add

theorem piKronecker_smul_univ [CommSemiring α] (c : ι → α) (A : Π i, Matrix (l i) (m i) α) :
    (⨂ i, c i • A i) = (∏ i, c i) • (⨂ i, A i) := by
  simp [← toMultilinearMap_apply, MultilinearMap.map_smul_univ]

@[simp]
theorem piKronecker_trace [CommSemiring α] [DecidableEq ι] [∀ i, Fintype (m i)]
    (A : Π i, Matrix (m i) (m i) α) : trace (⨂ i, A i) = ∏ i, trace (A i) := by
  simp_rw [Matrix.trace, Matrix.diag, piKronecker_apply, Fintype.prod_sum]

theorem PiKronecker_smul_const [CommSemiring α] (a : α) (A : Π i, Matrix (l i) (m i) α) :
    (⨂ i, a • A i) = a^(Fintype.card ι) • (⨂ i, A i) := by
  simp [piKronecker_smul_univ]

theorem conjTranspose_piKronecker [CommMonoid α] [StarMul α] (A : Π i, Matrix (l i) (l i) α) :
    (⨂ i, A i)ᴴ = (⨂ i, (A i)ᴴ) := by
  ext; simp

theorem star_piKronecker [CommMonoid α] [StarMul α] (A : Π i, Matrix (l i) (l i) α) :
    star (⨂ i, A i) = (⨂ i, star (A i)) := by
  ext; simp

theorem piKronecker_isHermitian [CommMonoid α] [StarMul α] (A : Π i, Matrix (l i) (l i) α)
    (h : ∀ i, IsHermitian (A i)) : IsHermitian (⨂ i, A i) := by
  ext r s
  simp [fun x ↦ IsHermitian.apply (h x) (r x) (s x)]

section vecMul

variable [DecidableEq ι] [∀ i, Fintype (m i)]

@[simp]
theorem piKronecker_mulVec_piOuterProduct [CommSemiring α] (A : Π i, Matrix (l i) (m i) α)
    (v : Π i, m i → α) : (⨂ i, A i) *ᵥ (⨂ i, v i) = (⨂ i, (A i) *ᵥ (v i)) := by
  ext r
  simp [mulVec_eq_sum, Fintype.prod_sum, Finset.prod_mul_distrib]

end vecMul

/-

# WIP

The material below needs cleaning up. Main result is a formula for the
determinant of a Kronecker product.

-/


open Equiv Kronecker

/-- TBD: to be upstreamed to "Mathlib.Data.Finset". -/
@[simps! apply symm_apply, expose]
def Finset.univEquiv (α : Type*) [Fintype α] :
    (Finset.univ : Finset α) ≃ α :=
  Equiv.subtypeUnivEquiv (fun x => Finset.mem_univ x)

@[simps! apply symm_apply]
private def piUnivEquiv {ι : Type*} [Fintype ι] {m : ι → Type*} :
    ((i : ↥(Finset.univ : Finset ι)) → m ↑i) ≃ ((i : ι) → m i) :=
  Equiv.piCongrLeft' _ (Finset.univEquiv ι)

private theorem reindex_univ_piKronecker [CommSemiring α]
    {l m : ι → Type*} (A : Π i, Matrix (l i) (m i) α) :
  reindex piUnivEquiv.symm piUnivEquiv.symm (⨂ i : ι, A i)
    = (⨂ i : (Finset.univ : Finset ι), A i) := by
  ext
  simp

/- This equivalence is defined because `Finset.insertPiProdEquiv`
  doesn't boundle membership into the type. -/
private def insertPiProdEquiv' {ι : Type*} [DecidableEq ι] {l : ι → Type*}
    {a : ι} {s : Finset ι} (ha : a ∉ s) :
    ((i : ↥(insert a s)) → l i) ≃ l a × ((i : ↥s) → l i) :=
  (Equiv.piCongrLeft' _ (Finset.subtypeInsertEquivOption ha)).trans Equiv.piOptionEquivProd

omit [Fintype ι] in
private theorem piKronecker_eq_kronecker_piKronecker [CommMonoid α] [DecidableEq ι]
    (A : Π i, Matrix (l i) (m i) α) {a : ι} {s : Finset ι} (h : a ∉ s) :
    reindex (insertPiProdEquiv' h) (insertPiProdEquiv' h) (⨂ i : (insert a s : Finset ι), A i) =
      (A a) ⊗ₖ (⨂ i : s, A i.val) := by
  rw [←Equiv.eq_symm_apply]
  ext p q
  simp only [piKronecker_apply, Finset.univ_eq_attach, ← Finset.prod_coe_sort_eq_attach,
    reindex_symm, reindex_apply, symm_symm, submatrix_apply, kroneckerMap_apply]
  rw [Fintype.prod_equiv (Finset.subtypeInsertEquivOption h)
    (fun i => A (i.val) (p i) (q i))
    (fun x => match x with
      | none => A a (p ⟨a, by simp⟩) (q ⟨a, by simp⟩)
      | some i => A i (p ⟨i, by simp⟩) (q ⟨i, by simp⟩)
    ) (by grind [Finset.subtypeInsertEquivOption])]
  simp
  rfl

open Fintype Finset in
omit [Fintype ι] in
theorem PiKronecker_det_dep {α : Type*} [CommRing α] [DecidableEq ι] [∀ i, DecidableEq (m i)]
    [∀ i, Fintype (m i)] (A : Π i, Matrix (m i) (m i) α) (s : Finset ι) :
    det (⨂ i : s, A i) = ∏ i ∈ s, det (A i) ^ ∏ j ∈ s.erase i, card (m j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [← Matrix.det_reindex_self (insertPiProdEquiv' ha),
      piKronecker_eq_kronecker_piKronecker, det_kronecker,
      Fintype.card_pi, ih, Finset.prod_insert ha, ← Finset.prod_pow]
    simp only [Finset.univ_eq_attach, ← pow_mul, Finset.erase_insert_eq_erase, ha,
      not_false_eq_true, Finset.erase_eq_of_notMem]
    congr! with u hu
    · symm; rw [← Finset.prod_coe_sort, Finset.univ_eq_attach]
    · by_cases hua : a = u
      · exact absurd hu (hua ▸ ha)
      · rw [Finset.erase_insert_of_ne hua,
          ← Finset.prod_erase_mul (s := insert a (s.erase u)) (a := a)
          (f := fun i => card (m i)) (by simp), Finset.erase_insert (by grind)]

variable {m : Type*} in
open Fintype in
theorem PiKronecker_det {α : Type*} [CommRing α] [DecidableEq ι] [DecidableEq m] [Fintype m]
    (A : ι → Matrix m m α) : det (⨂ i, A i) = ∏ i, det (A i) ^ card m ^ (card ι - 1) := by
  rw [← Matrix.det_reindex_self (piUnivEquiv.symm), reindex_univ_piKronecker]
  simp [PiKronecker_det_dep (s := Finset.univ (α := ι)) (A := A)]

end Kronecker

end Matrix
