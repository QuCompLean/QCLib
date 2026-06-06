/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import QCLib.Mathlib.LinearAlgebra.PiOuterProduct

/-!

# Kronecker products of unitary matrices

## Main definitions

* An `OuterProduct` instance for `Matrix.unitaryGroup`

## Maturity

Stable.

-/

public section

namespace Matrix

open scoped PiOuterProduct

variable {ι : Type*} [Fintype ι] {l m n : ι → Type*} {α : Type*}
variable {R : Type*}

variable [DecidableEq ι] [∀ i, DecidableEq (n i)] [∀ i, Fintype (n i)] [CommRing R] [StarRing R]

theorem piKronecker_mem_unitaryGroup (U : Π i, Matrix (n i) (n i) R)
    (hU : ∀ i, U i ∈ unitaryGroup (n i) R) : (⨂ i, U i) ∈ unitaryGroup (Π i, n i) R := by
  simp [mem_unitaryGroup_iff, mul_piKronecker_mul, star_piKronecker,
    fun i ↦ mem_unitaryGroup_iff.mp (hU i)]

/-- Kronecker product of a family of unitaries -/
def PiKroneckerUnitary (U : Π i, unitaryGroup (n i) R) : (unitaryGroup (Π i, n i) R) :=
  ⟨⨂ i, (U i : Matrix (n i) (n i) R), by simp [piKronecker_mem_unitaryGroup]⟩

instance : PiOuterProduct (fun i ↦ unitaryGroup (n i) R) (unitaryGroup (Π i, n i) R) where
  tprod := PiKroneckerUnitary

theorem piKron_unitary_def (U : Π i, unitaryGroup (n i) R) :
    (⨂ i, U i) = PiKroneckerUnitary U := rfl

@[simp]
theorem piKroneckerUnitary_apply (U : Π i, unitaryGroup (n i) R) (r : Π i, n i) (s : Π i, n i) :
    (⨂ i, U i) r s =  ∏ i, U i (r i) (s i) := by
  simp [piKron_unitary_def, PiKroneckerUnitary]

@[simp, norm_cast]
theorem coe_piKroneckerUnitary (U : Π i, unitaryGroup (n i) R) :
    (⨂ i, U i) = ⨂ i, ((U i) : Matrix (n i) (n i) R) := by rfl

@[simp]
theorem mul_piKroneckerUnitary_mul (U V : Π i, unitaryGroup (n i) R) :
    (⨂ i, U i) * (⨂ i, V i) = ⨂ i, U i * V i := by
  ext
  simp [mul_piKronecker_mul]

@[simp]
theorem piKroneckerUnitary_one :
    (⨂ i, (1 : unitaryGroup (n i) R)) = (1 : unitaryGroup (Π i, n i) R) := by
  simp [piKron_unitary_def, PiKroneckerUnitary]

theorem piKroneckerUnitary_smul_univ (c : ι → unitary R) (U : Π i, unitaryGroup (n i) R) :
    (⨂ i, c i • U i) = (∏ i, c i) • (⨂ i, U i) := by
  apply Subtype.ext
  simp [Submonoid.smul_def, piKronecker_smul_univ]

@[simp]
theorem piKroneckerUnitary_inv (U : Π i, unitaryGroup (n i) R) : (⨂ i, U i)⁻¹ = ⨂ i, (U i)⁻¹ :=
  inv_eq_of_mul_eq_one_left (by simp)

@[simp]
theorem piKroneckerUnitary_coe_mulVec (U : Π i, unitaryGroup (n i) R) (v : Π i, n i → R) :
    ↑(⨂ i, U i) *ᵥ (⨂ i, v i) = ⨂ i, (U i : Matrix (n i) (n i) R) *ᵥ (v i) := by
  simp

end Matrix
