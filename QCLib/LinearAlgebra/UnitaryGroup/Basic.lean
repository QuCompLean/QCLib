/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.Data.Complex.Basic
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.Lemmas
public import QCLib.LinearAlgebra.UnitaryGroup.DiagonalSubgroup
public import QCLib.LinearAlgebra.UnitaryGroup.Action -- always imported along with basic file

/-!

# Basic setup related to `Matrix.unitaryGroup`

`Simp` lemmas, notation, and results that are too specific for Mathlib.

-/

@[expose] public section

namespace Matrix

section Simp

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
theorem mul_kronecker_mul_symm
  {α l m n l' m' n' : Type*} [Fintype m] [Fintype m'] [CommSemiring α]
  (A : Matrix l m α) (B : Matrix m n α) (A' : Matrix l' m' α) (B' : Matrix m' n' α) :
  A ⊗ₖ A' * B ⊗ₖ B' = (A * B) ⊗ₖ (A' * B') := (Matrix.mul_kronecker_mul A B A' B').symm

-- Allows `simp` to prove what's called `Matrix.neg_unitary_val` in Lean-QuantumInfo
attribute [simp] Unitary.coe_neg

end Simp

section Notation

open Complex

notation "𝐔[" t "]" => Matrix.unitaryGroup t ℂ
notation "𝐃[" t "]" => Matrix.UnitaryGroup.diagonalSubgroup t ℂ

end Notation

end Matrix
