/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.PiKronecker
public import QCLib.Mathlib.Lemmas
public import QCLib.LinearAlgebra.UnitaryGroup.Basic
public import QCLib.Circuit.Gate.Qubit
public import QCLib.Circuit.Hadamard
public import QCLib.Misc.IntCast

/-!

# X- and Z-type operators

This file defines the generators of the `n`-qubit Pauli group and proves basic properties.

These will be used in `PauliGroup.lean` to define the full `n`-qubit Pauli group.

## Main definitions

* `ZZ p` for `p : Fin n → ℤ` is the `n`-qubit `Z`-type Pauli group element
* `XX q` for `q : Fin n → ℤ` is the `n`-qubit `X`-type Pauli group element

## Implementation notes

The arguments only enter modulo two, but making them integers makes it easier to
reason about the composition law of the full Pauli group.

## To do

Choose a namespace.
-/

public section

open Complex Matrix Qubit

open scoped PiOuterProduct

variable {n}

/-- Pauli group element of `Z` type. -/
def ZZ (p : Fin n → ℤ) : 𝐔[Register n] := ⨂ i, Z ^ (p i)

/-- Pauli group element of `X` type. -/
def XX (q : Fin n → ℤ) : 𝐔[Register n] := ⨂ i, X ^ (q i)

@[simp]
theorem XX_mul (q q' : Fin n → ℤ) : XX q * XX q' = XX (q + q') := by
  simp_rw [XX, mul_piKroneckerUnitary_mul]
  ext
  simp [_root_.zpow_add]

@[simp]
theorem ZZ_mul (p p' : Fin n → ℤ) : ZZ p * ZZ p' = ZZ (p + p') := by
  simp_rw [ZZ, mul_piKroneckerUnitary_mul]
  ext
  simp [_root_.zpow_add]

open scoped PiOuterProduct Fin.IntCast

@[simp]
theorem XX_apply (q : Fin n → ℤ) (x : Register n) : (XX q) • δ[x] = δ[(x + ↑q)] := by
  simp [XX, basisVector_eq_prod]

@[simp]
theorem ZZ_apply (p : Fin n → ℤ) (x : Register n) :
    (ZZ p) • δ[x] = (-1 : ℂ)^(p ⬝ᵥ ↑x) • δ[x] := by
  simp [ZZ, basisVector_eq_prod, dotProduct, piOuterProduct_smul_univ,
    ← Finset.prod_zpow_eq_zpow_sum₀]

-- theorem ZZ_diagonal (p : Fin n → ℤ) : ZZ p =
--   Pi.Unitary.diagonal (fun x : Register n ↦ (ᵤ-1) ^ (p ⬝ᵥ ↑x)) := by
--   apply Matrix.UnitaryGroup.ext_smul_basis
--   simp only [ZZ_apply, Matrix.UnitaryGroup.diagonal_smul_basisVector]
--   intro i
--   push_cast [Submonoid.smul_def]
--   with_reducible rfl

@[simp]
theorem ZZ_HH_conj (p : Fin n → ℤ) : (HH n) * (ZZ p) * (HH n)⁻¹ = (XX p) := by
  simp [HH_def, ZZ, XX]
