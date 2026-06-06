/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.PiKronecker
public import QCLib.Mathlib.Lemmas
public import QCLib.Matrix.UnitaryGroup.Action
public import QCLib.Matrix.UnitaryGroup.Basic
public import QCLib.Misc.IntCast
public import QCLib.Circuit.Qubit

/-!
# `n`-qubit Hadamard gate

We define the `n`-qubit Hadamard gate. Its columns are the `ℤ₂ⁿ`-Fourier basis,
a.k.a. the Hadamard basis.

## Main definitions

* `HH`: The `n`-qubit Hadamard gate
* `HadamardBasisVector`: Elements of the Hadamard basis

## Main result

* `hadarmardBasisVector_eq_prod` The elements of the Hadamard basis factorize
-/

@[expose] public section

open Qubit Matrix
open scoped PiOuterProduct

variable (n : ℕ)

noncomputable def HH := ⨂ _ : Fin n, H

theorem HH_def : HH n = ⨂ _ : Fin n, H := by rfl

theorem HH_sq : (HH n) * (HH n) = 1 := by simp [HH_def]

theorem HH_isHermitian : Matrix.IsHermitian (HH n).val := by
  ext i j
  simp only [HH, coe_piKroneckerUnitary, conjTranspose_apply, piKronecker_apply, star_prod,
    RCLike.star_def]
  congr with k
  generalize ha : i k = a, hb : j k = b
  fin_cases a <;> fin_cases b <;> simp [H_eq]

/-- `ℤ₂ⁿ` Fourier basis vector, aka a Hadamard basis vector. -/
noncomputable def HadamardBasisVector (k : Register n) :=
  (√2 : ℂ)⁻¹ ^ n • ∑ l : Register n, (-1 : ℂ)^(∑ i, (k i) * (l i) : ℕ) • δ[l]

private theorem HH_aux (y : Fin 2) :
    (δ[0] + (-1 : ℂ) ^ (y : ℕ) • δ[1]) = ∑ j : Fin 2, (-1 : ℂ) ^ ((y * j) : ℕ) • δ[j] := by
  simp [Pi.smul_def]

-- TBD: `simp` runs into a loop. Investigate.
theorem HH_apply (k : Register n) : (HH n) • δ[k] = HadamardBasisVector n k := by
  simp_rw [HH_def, HadamardBasisVector, basisVector_eq_prod, piKroneckerUnitary_smul_vec, H_apply,
    piOuterProduct_smul_const, HH_aux, piOuterProduct_univ_sum, Fintype.card_fin,
    piOuterProduct_smul_univ, Finset.prod_pow_eq_pow_sum]

theorem HH_hadarmardBasis (k : Register n) : (HH n) • HadamardBasisVector n k = δ[k] := by
  rw [← inv_eq_of_mul_eq_one_right (HH_sq n)]
  exact ((smul_eq_iff_eq_inv_smul (HH n)).mp  (HH_apply n k)).symm

theorem hadarmardBasisVector_eq_prod (k : Register n) :
    HadamardBasisVector n k = ⨂ i, Z ^ (k i : ℕ) • pls := by
  simp_rw [Z_pow_pls, HH_aux, piOuterProduct_smul_const, piOuterProduct_univ_sum,
    piOuterProduct_smul_univ, HadamardBasisVector, basisVector_eq_prod, Fintype.card_fin,
    Finset.prod_pow_eq_pow_sum]
