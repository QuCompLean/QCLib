/-
Copyright (c) 2026 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import QCLib.Mathlib.LinearAlgebra.PiOuterProduct
public import QCLib.LinearAlgebra.UnitaryGroup.Basic

import QCLib.Tactic.MatrixExpand
import QCLib.Mathlib.Lemmas

/-!
# Bases

## Main definitions

* `BasisVector`, a synonym for `Pi.basisFun ℂ`
* `Qubit` for `Fin 2`, so that the vector space for a single qubit is `Qubit → ℂ`
* `Register n` for `(Fin n) → Qubit`, so that the vector space for `n` qubits is `Register n → ℂ`

## Main results

* `basisVector_eq_prod` standard basis functions factorize

This file also collects `•` application

## Notation

* `δ[i]` for `BasisVector i`

-/

@[expose] public section

noncomputable def BasisVector {ι : Type*} [Finite ι] (i : ι) : (ι → ℂ) :=
  Pi.basisFun ℂ ι i

@[matrixExpand]
theorem basisVector_def (ι : Type*) [Finite ι] (i : ι) :
  BasisVector i = Pi.basisFun ℂ ι i := by rfl

-- TBD: scope
/-- The computational basis. -/
notation3:max "δ[" i:90 "] " =>
  BasisVector i

-- `ext` lemma stated for `SMul` action of unitaries on vectors.
-- TBD: Get rid of this? Formulate in terms of `toLin` and general Bases? State
-- for `MatrixLike` objects?
-- More generally, decide whether to use `•` for actions on vectors
theorem Matrix.UnitaryGroup.ext_smul_basis (ι : Type*) [Fintype ι] [DecidableEq ι]
  (U V : Matrix.unitaryGroup ι ℂ) : (∀ i : ι, ((U • δ[i]) : ι → ℂ) = V • δ[i]) → U = V := by
  simp only [basisVector_def, Pi.basisFun_apply, Subtype.ext_iff, Submonoid.smul_def,
    smul_eq_mulVec, mulVec_single, MulOpposite.op_one, one_smul]
  apply Matrix.ext_col

section SMul

@[simp]
theorem Matrix.UnitaryGroup.diagonal_smul_basisVector (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d : ι → unitary ℂ) (i : ι) : (Pi.Unitary.diagonal d) • δ[i] = (d i) • δ[i] := by
  ext j
  simp only [Submonoid.smul_def]
  push_cast
  simp [basisVector_def, Pi.single_apply]

-- TBD: `_apply_basis` → `_smul`? In any case, make consistent.

-- TBD: Debug this.

theorem diagonalSubgroup_apply_basis {α} [DecidableEq α] [Fintype α] (D : 𝐃[α]) (k : α) :
    D • δ[k] = D k k • δ[k] := by
  obtain ⟨d, hd⟩ := Pi.Unitary.mem_diagonalSubgroup.mp D.prop
  simp [basisVector_def, ← hd, ← Pi.single_smul, Subgroup.smul_def, Submonoid.smul_def]

theorem finset_prod_diagonalSubgroup_apply_basis {ι} (s : Finset ι)
    {α} [DecidableEq α] [Fintype α] (D : ι → 𝐃[α]) (k : α) :
    (∏ i ∈ s, D i) • δ[k] = (∏ i ∈ s, D i k k) • δ[k] := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, mul_comm, ← smul_eq_mul,
      smul_assoc, diagonalSubgroup_apply_basis, smul_comm]
    simp_all

theorem finset_prod_diagonalSubgroup_pow_apply_basis {ι} (s : Finset ι)
    {α} [DecidableEq α] [Fintype α] (D : ι → 𝐃[α]) (k : α) (b : ℕ) :
    (∏ i ∈ s, (D i) ^ b) • δ[k] = (∏ i ∈ s, (D i k k) ^ b) • δ[k] := by
  simp [diagonalSubgroup_coe_pow_apply, finset_prod_diagonalSubgroup_apply_basis]

end SMul

section Qubits

abbrev Qubit := Fin 2
abbrev Register (n : Nat) := (Fin n) → Qubit

open Complex Matrix
open scoped PiOuterProduct

/-- Computational basis vectors factorize -/
theorem basisVector_eq_prod {n : ℕ} (k : Register n) : δ[k] = ⨂ i, δ[(k i)] := by
  ext
  simp [basisVector_def, Pi.single_eq_prod]

end Qubits

end
