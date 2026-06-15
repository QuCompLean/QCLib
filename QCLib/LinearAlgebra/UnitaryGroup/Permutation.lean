/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import QCLib.Logic.Equiv
public import QCLib.LinearAlgebra.UnitaryGroup.Basic
public import QCLib.LinearAlgebra.StdBasis

/-!

# Permutations as unitary matrices

## Main definitions

* `permHom`: The standard unitary representation of the permutation group
* `permSubsystemsHom`: Permutations of subsystems

## Main results

Actions on standard basis elements.

-/

@[expose] public section

variable (R : Type*) [CommRing R] [StarRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Equiv Matrix

namespace Matrix.UnitaryGroup

/-- The action of a permutation on the domain of a function as a Monoid homomorphism. -/
@[simps]
def arrowCongrLeftHom {ι : Type*} (n : Type*) : (Perm ι) →* Perm (ι → n) where
  toFun σ := arrowCongr σ (Equiv.refl n)
  map_one' := by ext; simp [pull_end]
  map_mul' x y := by simp [Equiv.Perm.mul_def, Equiv.arrowCongrLeft_trans]

/-- Permutations of basis vectors as unitary matrices -/
@[simps]
def permHom : Perm n →* unitaryGroup n R where
  toFun σ := ⟨σ⁻¹.permMatrix R, by
    simp [mem_unitaryGroup_iff, star_eq_conjTranspose, ← permMatrix_mul]⟩
  map_one' := by simp
  map_mul' := by simp

-- base `arrowCongrLeftHom` on `piCongrLeft'`?
theorem arrowCongrLeftHom_apply_eq_piCongrLeft' {ι : Type*} (n : Type*) (σ : Perm ι) :
    arrowCongrLeftHom n σ = piCongrLeft' _ σ := by ext; simp

@[simp]
theorem perm_smul_basisVector (σ : Perm n) (k : n) : (permHom ℂ σ) • δ[k] = δ[σ k] := by
  ext l
  simp [Submonoid.smul_def, basisVector_def]
  grind

@[simp]
theorem unitary_mul_perm_apply_apply (σ : Perm n) (U : unitaryGroup n R) (k l : n) :
    (U * (permHom R σ)) k l = (U k (σ l)) := by
  push_cast
  simp [PEquiv.mul_toMatrix_toPEquiv]
  rfl -- TBD: Figure out `Equiv.symm` API.

@[simp]
theorem perm_mul_unitary_apply_apply (σ : Perm n) (U : unitaryGroup n R) (k l : n) :
    ((permHom R σ) * U ) k l = (U (σ⁻¹ k) l) := by
  push_cast
  simp [PEquiv.toMatrix_toPEquiv_mul]

variable (n) in
/-- Permutations of subsystems -/
def permSubsystemsHom : Perm ι →* unitaryGroup (ι → n) R :=
  (permHom R).comp (arrowCongrLeftHom n)

theorem permSubsystemsHom_eq_permHom (σ : Perm ι) :
  permSubsystemsHom R n σ = permHom R (arrowCongrLeftHom n σ) := rfl

theorem permSubsystemsHom_smul_eq (σ : Perm ι) (v : (ι → n) → R) :
    (permSubsystemsHom R n σ) • v = (permHom R (arrowCongrLeftHom n σ)) • v := by
  simp [permSubsystemsHom]

@[simp]
theorem permSubsystemsHom_apply_apply (σ : Perm ι) (k : ι → n) :
    (permSubsystemsHom ℂ n σ) • δ[k] = δ[arrowCongrLeftHom n σ k] := by
  simp [permSubsystemsHom_smul_eq]

end Matrix.UnitaryGroup


end
