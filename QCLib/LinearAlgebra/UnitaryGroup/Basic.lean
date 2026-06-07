/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.Data.Complex.Basic
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.Lemmas
public import QCLib.LinearAlgebra.UnitaryGroup.Action -- always imported along with basic file

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

-- Rewrites the membership condition for `unitary` in a way that's compatible
-- with the one of `unitaryGroup`.
@[to_additive]
theorem mul_and_mul_iff_mul {M} [MulOne M] [IsDedekindFiniteMonoid M] {a b : M} :
    a * b = 1 ∧ b * a = 1 ↔ b * a = 1 := ⟨And.right, fun h ↦ ⟨mul_eq_one_comm.mpr h, h⟩⟩

end Simp

-- -- move somehwere
-- section new
--
-- #check Matrix.UnitaryGroup.coeFun
-- #check Matrix.diagonal
-- #check Matrix.diagonalAlgHom
--
-- namespace Matrix.UnitaryGroup
--
-- -- We assume `[CommRing R]` to avoid having to treat left and right inverses separetely.
-- -- TBD: Generalize?
-- variable {R : Type*} [CommRing R] [StarRing R]
-- variable {n : Type*} [DecidableEq n] [Fintype n]
--
-- /-- Star monoid equivalence between unitary-valued functions and unitary functions -/
-- @[simps]
-- def diagonalMonoidHom : (n → unitary R) →* (unitaryGroup n R) where
--   toFun d := ⟨Matrix.diagonalAlgHom R (fun i ↦ ↑(d i)), by
--     simp
--
--     ⟩
--   invFun d := fun i ↦ ⟨d i, (mem_unitary ⇑d).mp (SetLike.coe_mem d) i⟩
--   map_mul' x y := by with_reducible_and_instances rfl
--   map_star' x := by with_reducible_and_instances rfl
--
-- end new
--
