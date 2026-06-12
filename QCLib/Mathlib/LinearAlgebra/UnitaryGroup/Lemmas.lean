/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.ZPow
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!

# Misc lemmas and defs connected to `Matrix.unitaryGroup`

## To do

`variable` declarations are all over the place.

-/

@[expose] public section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {α : Type*} [CommRing α] [StarRing α]
variable {ι : Type*} [DecidableEq ι]

section Reindex

variable (R : Type*) [CommSemiring R]
variable (A : Type*) [Semiring A] [Algebra R A] [Star A]
variable (e : m ≃ n)
variable (M N : Matrix m m A)

theorem reindexAlgEquiv_map_star :
    star (reindexAlgEquiv R A e M) = reindexAlgEquiv R A e (star M) := by
  simp_rw [reindexAlgEquiv_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]

@[simps!]
def reindexStarAlgEquiv : Matrix m m A ≃⋆ₐ[R] Matrix n n A :=
  { Matrix.reindexAlgEquiv R A e with
    map_star' M := by
      change reindexAlgEquiv R A e (star M) = star (reindexAlgEquiv R A e M)
      exact reindexAlgEquiv_map_star R A e M
    map_smul' := by simp }

theorem reindexStarAlgEquiv_mul :
    (reindexStarAlgEquiv R A e) (M * N) =
      (reindexStarAlgEquiv R A e) M * (reindexStarAlgEquiv R A e) N := by
  simp

theorem reindexStarAlgEquiv_injective : Function.Injective (reindexStarAlgEquiv R A e) := by
  intro a b h
  ext i j
  simpa using congr_fun₂ h (e i) (e j)

@[simps!]
def reindexMonoidEquiv : (unitaryGroup m α) ≃* unitaryGroup n α where
  toFun U := ⟨reindexStarAlgEquiv α α e U, by
    rw [mem_unitaryGroup_iff, ← map_star]
    simp⟩
  invFun U := ⟨reindexStarAlgEquiv α α e.symm U, by
    rw [mem_unitaryGroup_iff, ← map_star]
    simp⟩
  map_mul' := by simp
  left_inv U := by simp
  right_inv U := by simp

end Reindex

section Coe

@[norm_cast]
theorem UnitaryGroup.coe_inv (U : unitaryGroup n α) :
    ((U⁻¹ : unitaryGroup n α) : Matrix n n α) = (U : Matrix n n α)⁻¹ := by
  refine (Matrix.inv_eq_left_inv ?_).symm
  simp

@[norm_cast]
theorem UnitaryGroup.coe_zpow (z : ℤ) (U : unitaryGroup n α) :
    (((U ^ z) : (unitaryGroup n α)) : Matrix n n α) = (U : Matrix n n α) ^ z := by
  cases z
  · simp [SubmonoidClass.coe_pow]
  · simp only [zpow_negSucc, Matrix.UnitaryGroup.coe_inv, SubmonoidClass.coe_pow]

end Coe

section Diagonal

@[simp]
theorem star_diagonal {α : Type*} [NonUnitalNonAssocSemiring α] [StarRing α]
    (f : ι → α) : star (Matrix.diagonal f) = Matrix.diagonal (star f) := by
  ext i j
  by_cases h : i = j
  · simp [h]
  · replace h : i ≠ j := by grind
    simp [h, h.symm]

@[simp]
theorem diagonal_mem_unitaryGroup_iff (f : n → α) :
    Matrix.diagonal f ∈ unitaryGroup n α ↔ ∀ i, f i ∈ unitary α := by
  simp [Unitary.mem_iff, funext_iff, forall_and]

/-- MonoidHom from phase-valued functions to diagonal unitaries -/
@[simps]
def UnitaryGroup.diagonalMonoidHom : (n → unitary α) →* unitaryGroup n α where
  toFun d := ⟨Matrix.diagonal fun i ↦ d i, by simp⟩
  map_one' := by simp
  map_mul' := by simp

omit [StarRing α] [DecidableEq ι]

lemma List.prod_diagonal_map (l : List ι) (f : ι → n → α) :
    (l.map (fun i => Matrix.diagonal (f i))).prod
      = Matrix.diagonal (fun j => (l.map (fun i => f i j)).prod) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp [List.map_cons, List.prod_cons, ih, Matrix.diagonal_mul_diagonal]

lemma Fisnet.prod_diagonal (s : Finset ι) (f : ι → n → α) :
    (s.toList.map (fun i => Matrix.diagonal (f i))).prod
      = Matrix.diagonal (fun j => ∏ i ∈ s, f i j) := by
  simp [List.prod_diagonal_map, Finset.prod_eq_multiset_prod,
    ← Multiset.prod_toList, Finset.toList]

end Diagonal


section BlockDiagonal

@[simp]
theorem star_blockDiagonal {α m : Type*} [NonUnitalNonAssocSemiring α] [StarRing α]
    (f : ι → Matrix m m α) : star (Matrix.blockDiagonal f) = Matrix.blockDiagonal (star f) := by
  simp [Pi.star_def, star_eq_conjTranspose]

variable {o : Type*} [Fintype o] [DecidableEq o]

@[simp]
theorem blockDiagonal_mem_unitaryGroup_iff (f : o → Matrix m m α) :
    Matrix.blockDiagonal f ∈ unitaryGroup (m × o) α ↔ ∀ i, f i ∈ unitaryGroup m α := by
  refine Iff.intro (fun h ↦ ?_) (fun h ↦ ?_)
  all_goals simp_all only [mem_unitaryGroup_iff, star_eq_conjTranspose, blockDiagonal_conjTranspose,
    ← blockDiagonal_mul, ← Pi.one_def, ← blockDiagonal_one]
  simpa only [blockDiag_blockDiagonal, Pi.one_apply] using fun k ↦ congrArg (blockDiag (k := k)) h

@[simps]
def UnitaryGroup.blockDiagonalMonoidHom : (o → unitaryGroup m α) →* unitaryGroup (m × o) α where
  toFun d := ⟨Matrix.blockDiagonal fun i ↦ d i, by simp ⟩
  map_one' := by simp [← Pi.one_def]
  map_mul' := by simp


-- TBD: Are all these combinations needed?

@[simps!]
def UnitaryGroup.blockDiagonalStarMonoidHom :
    (o → unitaryGroup m α) →⋆* unitaryGroup (m × o) α where
  toMonoidHom := blockDiagonalMonoidHom
  map_star' d := by
    apply Subtype.ext
    simp [star_eq_conjTranspose, Unitary.coe_star]

@[simps!]
def blockDiagonalAlgHom :
    (o → Matrix m m α) →ₐ[α] Matrix (m × o) (m × o) α where
  toRingHom := blockDiagonalRingHom m o α
  commutes' r := by
    ext
    simp [algebraMap_matrix_apply, blockDiagonal_apply]
    grind

@[simps!]
def blockDiagonalStarAlgHom :
    (o → Matrix m m α) →⋆ₐ[α] Matrix (m × o) (m × o) α where
  toAlgHom := blockDiagonalAlgHom
  map_star' M := by simp [star_eq_conjTranspose, blockDiagonal_conjTranspose, Pi.star_def]

end BlockDiagonal

end Matrix
