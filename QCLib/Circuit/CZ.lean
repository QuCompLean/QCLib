/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module


public import QCLib.Circuit.Gate.Qubit
public import QCLib.Circuit.Gate.Bipartite
public import QCLib.Circuit.Embed

/-!

# Controlled-Z operations on multiple qubits

Special-case this family of gates, because it allows for a formula that unifies
bipartite controlled-`Z` gates and single-body `Z` gates.

TBD: Keep?

-/

@[expose] public section

open Matrix Matrix.UnitaryGroup Qubit

open scoped PiOuterProduct

open Matrix

variable {n : ℕ} (i j : Fin n)


/-- The main diagonal of the controlled-`Z` gate. Degenerates to a `Z` gate for `i=j`. -/
def CZFun (k : Register n) : unitary ℂ := (ᵤ-1) ^ (k i * k j : ℕ)

theorem CZFun_def : CZFun i j = fun k ↦ (ᵤ-1) ^ (k i * k j : ℕ) := rfl

/-- The controlled-Z gate between qubits `i` and `j`. Degenerates to a Z gate if `i=j`. -/
noncomputable def CZ : 𝐔[Register n] := diagonalMonoidHom (CZFun i j)

theorem CZ_def : CZ i j = diagonalMonoidHom (CZFun i j) := rfl

theorem CZ_eq_controlled_of_neq (h : i ≠ j) : CZ i j = bipartite i j C[Z] := by
  simp only [Z_diagonal, CZ_def, CZFun_def, controllize_diagonal, bipartite_diagonal]
  congr
  ext k
  simp only [SubmonoidClass.coe_pow, Fin.toNat_eq_val]
  ring_nf

theorem CZ_eq_Z_of_eq (h : i = j) : CZ i j = single i Z := by
  simp only [Z_diagonal, CZ_def, CZFun_def, single_diagonal]
  congr
  ext k
  generalize heq : k j = x
  fin_cases x  <;> simp [h, heq]

@[simp]
theorem CZ_symm : CZ i j = CZ j i := by simp [CZ_def, CZFun_def, mul_comm]
