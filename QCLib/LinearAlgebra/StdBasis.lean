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
notation3:max "δ[" i:90 "] " => BasisVector i

-- `ext` lemma stated for `SMul` action of unitaries on vectors.
-- TBD: Get rid of this? Formulate in terms of `toLin` and general Bases? State
-- for `MatrixLike` objects?
-- More generally, decide whether to use `•` for actions on vectors
theorem Matrix.UnitaryGroup.ext_smul_basis (ι : Type*) [Fintype ι] [DecidableEq ι]
  (U V : Matrix.unitaryGroup ι ℂ) : (∀ i : ι, ((U • δ[i]) : ι → ℂ) = V • δ[i]) → U = V := by
  simp only [basisVector_def, Pi.basisFun_apply, Subtype.ext_iff, Submonoid.smul_def,
    smul_eq_mulVec, mulVec_single, MulOpposite.op_one, one_smul]
  apply Matrix.ext_col

@[simp]
theorem Matrix.UnitaryGroup.diagonal_smul_basisVector (ι : Type*) [Fintype ι] [DecidableEq ι]
    (d : ι → unitary ℂ) (i : ι) : (diagonalMonoidHom d) • δ[i] = (d i) • δ[i] := by
  ext j
  simp [Submonoid.smul_def, basisVector_def, Pi.single_apply]

@[simp]
theorem Matrix.diagonal_smul_basisVector
  {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℂ) (v : ι) :
    Matrix.diagonal d • δ[v] = d v • δ[v] := by
  ext i
  simp [basisVector_def, Pi.basisFun_apply, Pi.single_apply]

section SMul

section Qubits

abbrev Qubit := Fin 2
abbrev Register (n : Nat) := (Fin n) → Qubit

open Complex Matrix
open scoped PiOuterProduct

theorem basisVector_eq_prod {d} {n : ℕ} (k : Fin n → Fin d) : δ[k] = ⨂ i, δ[(k i)] := by
  ext
  simp [basisVector_def, Pi.single_eq_prod]

end Qubits
