/-
Copyright (c) 2026 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
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

public section

open EuclideanSpace

variable {ι : Type*} [Fintype ι]

noncomputable def BasisVector (i : ι) : (ι → ℂ) :=
  basisFun ι ℂ i

@[matrixExpand]
theorem basisVector_def (i : ι) :
  BasisVector i = basisFun ι ℂ i := by rfl

-- TBD: scope
/-- The computational basis. -/
notation3:max "δ[" i:90 "] " => BasisVector i

-- `ext` lemma stated for `SMul` action of unitaries on vectors.
-- TBD: Get rid of this? Formulate in terms of `toLin` and general Bases? State
-- for `MatrixLike` objects?
-- More generally, decide whether to use `•` for actions on vectors
-- Move to other module?
theorem Matrix.UnitaryGroup.ext_col {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Matrix.unitaryGroup ι ℂ} :
    (∀ i : ι, (U : Matrix ι ι ℂ).col i = (V : Matrix ι ι ℂ).col i) → U = V := by
  intro h
  apply Subtype.ext
  exact Matrix.ext_col h

theorem Matrix.UnitaryGroup.ext_smul_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {U V : Matrix.unitaryGroup ι ℂ} : (∀ i : ι, ((U • δ[i]) : ι → ℂ) = V • δ[i]) → U = V := by
   simpa [basisVector_def, Submonoid.smul_def] using ext_col

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
  simp [basisVector_def, basisFun_apply, Pi.single_apply]

theorem Matrix.UnitaryGroup.apply_basis {ι : Type*} [Fintype ι]
    [DecidableEq ι] {U : Matrix.unitaryGroup ι ℂ} (v : ι) :
    U • δ[v] = ∑ i, U i v • δ[i] := by
  ext
  simp [basisVector_def, Pi.single_apply, Submonoid.smul_def]

section SMul

section Qubits

abbrev Qubit := Fin 2
abbrev Register (n : Nat) := (Fin n) → Qubit

open Complex Matrix
open scoped PiOuterProduct

theorem basisVector_eq_prod {d} {n : ℕ} (k : Fin n → Fin d) : δ[k] = ⨂ i, δ[(k i)] := by
  ext
  simp [basisVector_def, ← Pi.single_eq_prod, ← Pi.single_apply]

end Qubits
