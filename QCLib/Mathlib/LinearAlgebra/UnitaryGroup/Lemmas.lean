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

-/

@[expose] public section

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {α : Type v} [CommRing α] [StarRing α]

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
  left_inv := fun U ↦ by simp
  right_inv := fun U ↦ by simp

end Reindex

/-
For square matrices, we've got `Matrix.star_eq_conjTranspose`. However, some
results are only stated for `star` and some only for `conjTranspose`. We can't
standardize on `star`, because we need also use non-square matrices. Thus, we
reprove re-prove some `star` theorems for `conjTranspose`, so that one doesn't
have to switch back and forth.
-/
section StarConjTranspose

variable (A : Matrix n n α)

-- #check Unitary.mul_star_self_of_mem
@[simp]
theorem UnitaryGroup.conjTranspose_mul_self_of_mem (hU : A ∈ Matrix.unitaryGroup n α) :
    A * Aᴴ = 1 := by
  simp [mem_unitaryGroup_iff.mp hU, ← star_eq_conjTranspose]

-- #check Unitary.star_mul_self_of_mem
@[simp]
theorem UnitaryGroup.conjTranspose_mul_self_of_mem' (hU : A ∈ Matrix.unitaryGroup n α) :
    Aᴴ * A = 1 := by
  simp [mem_unitaryGroup_iff'.mp hU, ← star_eq_conjTranspose]

end StarConjTranspose

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
theorem star_diagonal {ι α : Type*} [NonUnitalNonAssocSemiring α] [DecidableEq ι] [StarRing α]
    (f : ι → α) : star (Matrix.diagonal f) = Matrix.diagonal (star f) := by
  ext i j
  by_cases h : i = j
  · simp [h]
  · have : i ≠ j := by grind
    simp [this, this.symm]

@[simp]
theorem diagonal_mem_unitaryGroup_iff (f : n → α) :
    Matrix.diagonal f ∈ unitaryGroup n α ↔ ∀ i, f i ∈ unitary α := by
  simp [Unitary.mem_iff, funext_iff, forall_and]

/-- MonoidHom from phase-valued functions to diagonal unitaries -/
def UnitaryGroup.diagonalMonoidHom : (n → unitary α) →* unitaryGroup n α where
  toFun d := ⟨Matrix.diagonal fun i ↦ (d i : α), by simp⟩
  map_one' := by simp
  map_mul' := by simp

end Diagonal


section BlockDiagonal

variable (R : Type*) (m o : Type*)
    [CommSemiring R] [StarRing R] [DecidableEq o] [DecidableEq m] [Fintype o] [Fintype m]

@[simps!]
def blockDiagonalAlgHom :
    (o → Matrix m m R) →ₐ[R] Matrix (m × o) (m × o) R where
  toRingHom := blockDiagonalRingHom m o R
  commutes' r := by
    ext
    simp [algebraMap_matrix_apply, blockDiagonal_apply]
    grind

@[simps!]
def blockDiagonalStarAlgHom :
    (o → Matrix m m R) →⋆ₐ[R] Matrix (m × o) (m × o) R where
  toAlgHom := blockDiagonalAlgHom R m o
  map_star' M := by
    simp [star_eq_conjTranspose, blockDiagonal_conjTranspose, Pi.star_def]

open Matrix in
@[simps]
def UnitaryGroup.blockDiagonalStarMonoidHom (R : Type*) [CommRing R] [StarRing R] :
    (o → unitaryGroup m R) →⋆* unitaryGroup (m × o) R where
  toFun d := ⟨ blockDiagonalStarAlgHom R m o (fun i : o => ↑(d i)), by
    simp only [blockDiagonalStarAlgHom_apply, mem_unitaryGroup_iff, star_eq_conjTranspose,
      blockDiagonal_conjTranspose, ← blockDiagonal_mul, ← blockDiagonal_one, blockDiagonal_inj]
    ext1
    simp [← star_eq_conjTranspose] ⟩
  map_one' := by ext1; simp [← Matrix.blockDiagonal_one, blockDiagonal_apply]
  map_mul' := by simp
  map_star' d := by apply Subtype.ext; simp [star_eq_conjTranspose, Unitary.coe_star]

end BlockDiagonal

end Matrix
