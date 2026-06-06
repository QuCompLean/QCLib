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

-- TBD: Put in different file.
section Neg

-- TBD: C.f. `orderOf_neg_one`
-- Makes `simp` realize that `(-1 : ℂ) ≠ 1`
@[simp]
theorem _root_.Ring.neg_one_ne_one_of_char_zero_class {α : Type*} [Ring α] [CharZero α] :
    (-1 : α) ≠ 1 := by
  simp [Ring.neg_one_ne_one_of_char_ne_two]

end Neg

end Matrix
