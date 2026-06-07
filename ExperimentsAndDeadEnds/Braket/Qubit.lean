/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Qml.Circuits.Qubit

@[expose] public section

open scoped Matrix Braket
open Matrix Qubit

@[simp]
theorem upup_plus_dndn_eq_id : ∣up⟩⟨up∣ + ∣dn⟩⟨dn∣ = 1 := by matrix_expand [up, dn, basisVector_def]

@[simp] theorem inner_updn_eq_zero : ⟪up, dn⟫ = 0 := by simp [up, dn, basisVector_def]
@[simp] theorem inner_dnup_eq_zero : ⟪dn, up⟫ = 0 := by simp [up, dn, basisVector_def]
@[simp] theorem inner_upup_eq_zero : ⟪up, up⟫ = 1 := by simp [up, basisVector_def]
@[simp] theorem inner_dndn_eq_zero : ⟪dn, dn⟫ = 1 := by simp [dn, basisVector_def]
