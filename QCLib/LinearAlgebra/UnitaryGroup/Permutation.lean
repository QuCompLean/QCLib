/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
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

section AreTheseInMathlib?

/-- Version of `Equiv.arrowCongr_trans` with trivial second permutation. -/
theorem Equiv.arrowCongrLeft_trans {α₁ α₂ α₃ β : Sort*} (e₁ : α₁ ≃ α₂) (e₂ : α₂ ≃ α₃) :
    arrowCongr (e₁.trans e₂) (Equiv.refl β)
      = (arrowCongr e₁ (Equiv.refl β)).trans (arrowCongr e₂ (Equiv.refl β)) := rfl

/-- The action of a permutation on the domain of a function as a Monoid homomorphism. -/
@[simps]
def Equiv.arrowCongrLeftHom {ι : Type*} (n : Type*) : (Perm ι) →* Perm (ι → n) where
  toFun σ := arrowCongr σ (Equiv.refl n)
  map_one' := by ext; simp [pull_end]
  map_mul' x y := by simp [Equiv.Perm.mul_def, Equiv.arrowCongrLeft_trans]

end AreTheseInMathlib?

variable (R : Type*) [CommRing R] [StarRing R]
variable {n : Type*} [Fintype n] [DecidableEq n]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open Equiv Matrix

namespace Matrix.UnitaryGroup

/-- Permutations of basis vectors as unitary matrices -/
@[simps]
def permHom : Perm n →* unitaryGroup n R where
  toFun σ := ⟨σ⁻¹.permMatrix R, by
    simp [mem_unitaryGroup_iff, star_eq_conjTranspose, ← permMatrix_mul]⟩
  map_one' := by simp
  map_mul' := by simp

@[simp]
theorem perm_smul_basisVector (σ : Perm n) (k : n) : (permHom ℂ σ) • δ[k] = δ[σ k] := by
  ext l
  simp [Submonoid.smul_def, basisVector_def]
  grind

variable (n) in
/-- Permutations of subsystems -/
@[simps!]
def permSubsystemsHom : Perm ι →* unitaryGroup (ι → n) R :=
  (permHom R).comp (arrowCongrLeftHom n)

theorem permSubsystemsHom_smul_eq (σ : Perm ι) (v : (ι → n) → R) :
    (permSubsystemsHom R n σ) • v = (permHom R (arrowCongrLeftHom n σ)) • v := by
  simp [permSubsystemsHom]

@[simp]
theorem permSubsystemsHom_apply_apply (σ : Perm ι) (k : ι → n) :
    (permSubsystemsHom ℂ n σ) • δ[k] = δ[arrowCongrLeftHom n σ k] := by
  simp [permSubsystemsHom_smul_eq]

end Matrix.UnitaryGroup


end
