/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.Data.Complex.Basic
public import QCLib.Mathlib.Lemmas
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.Lemmas

/-!

# Basic setup related to `Matrix.unitaryGroup`

`Simp` lemmas, notation, and results that are too specific for Mathlib.

-/

@[expose] public section

section Notation

open Complex

-- TBD: scope
notation "𝐔[" t "]" => Matrix.unitaryGroup t ℂ
notation "𝐃[" t "]" => t → unitary ℂ

end Notation

section Simp

open Matrix

-- `Map` versions create inconvenient side goals
-- TBD: Apparently, removing the simp attribute takes effect only in this module.
-- How can I make this persistent project-wide?
attribute [-simp] kroneckerMap_one_one

attribute [simp] conjTranspose_kronecker
attribute [simp] add_kronecker
attribute [simp] kronecker_add
attribute [simp] one_kronecker_one

open scoped Kronecker in
-- State the `.symm` version to add the `simp` attribute
@[simp]
theorem Matrix.mul_kronecker_mul_symm
  {α l m n l' m' n' : Type*} [Fintype m] [Fintype m'] [CommSemiring α]
  (A : Matrix l m α) (B : Matrix m n α) (A' : Matrix l' m' α) (B' : Matrix m' n' α) :
  A ⊗ₖ A' * B ⊗ₖ B' = (A * B) ⊗ₖ (A' * B') := (Matrix.mul_kronecker_mul A B A' B').symm

-- Allows `simp` to prove what's called `Matrix.neg_unitary_val` in Lean-QuantumInfo
attribute [simp] Unitary.coe_neg

-- TBD: Remove?
-- Rewrites the membership condition for `unitary` in a way that's compatible
-- with the one of `unitaryGroup`.
@[to_additive]
theorem mul_and_mul_iff_mul {M} [MulOne M] [IsDedekindFiniteMonoid M] {a b : M} :
    a * b = 1 ∧ b * a = 1 ↔ b * a = 1 := ⟨And.right, fun h ↦ ⟨mul_eq_one_comm.mpr h, h⟩⟩

variable {R : Type*} [CommRing R] [StarRing R]
variable {n : Type*} [DecidableEq n] [Fintype n]

@[simp]
theorem Matrix.UnitaryGroup.diagonal_zpow (d : n → unitary R) (z : ℤ) :
    (diagonalMonoidHom d) ^ z = diagonalMonoidHom (d ^ z) := (map_zpow _ _ _).symm

attribute [simp] Matrix.commute_diagonal

@[simp]
theorem Matrix.UnitaryGroup.commute_diagonal (d₁ d₂ : n → unitary R) :
    Commute (UnitaryGroup.diagonalMonoidHom d₁) (UnitaryGroup.diagonalMonoidHom d₂) := by
  apply Submonoid.coe_commute_iff.mp
  exact Matrix.commute_diagonal _ _

/-
For square matrices, we've got `Matrix.star_eq_conjTranspose`. However, some
results are only stated for `star` and some only for `conjTranspose`. We can't
standardize on `star`, because we need also use non-square matrices. Thus, we
reprove some `star` theorems for `conjTranspose`, so that one doesn't
have to switch back and forth.
-/
section StarConjTranspose

variable (A : Matrix n n R)

-- #check Unitary.mul_star_self_of_mem
@[simp]
theorem UnitaryGroup.conjTranspose_mul_self_of_mem (hU : A ∈ Matrix.unitaryGroup n R) :
    A * Aᴴ = 1 := by
  simp [mem_unitaryGroup_iff.mp hU, ← star_eq_conjTranspose]

-- #check Unitary.star_mul_self_of_mem
@[simp]
theorem UnitaryGroup.conjTranspose_mul_self_of_mem' (hU : A ∈ Matrix.unitaryGroup n R) :
    Aᴴ * A = 1 := by
  simp [mem_unitaryGroup_iff'.mp hU, ← star_eq_conjTranspose]

end StarConjTranspose

end Simp
