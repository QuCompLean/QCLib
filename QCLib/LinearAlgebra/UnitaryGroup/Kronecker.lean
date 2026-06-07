/-
Copyright (c) 2026 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import QCLib.LinearAlgebra.UnitaryGroup.Basic

/-!

# Unitary group and binary tensor product

TBD.

-/

@[expose] public section


open Matrix

section

open Kronecker Matrix

variable {α β γ} [CommRing γ] [StarRing γ]

/- Generalization of statement from @timeroot's repo -/
@[simp]
theorem star_kron (a : Matrix α α γ) (b : Matrix β β γ) : star (a ⊗ₖ b) = (star a) ⊗ₖ (star b) := by
  ext
  simp

variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem kron_unitary (a : unitaryGroup α γ) (b : unitaryGroup β γ) :
    ↑a ⊗ₖ ↑b ∈ unitaryGroup (α × β) γ := by
  simp [Matrix.mem_unitaryGroup_iff]

def unitary_kron (a : unitaryGroup α γ) (b : unitaryGroup β γ) : unitaryGroup (α × β) γ :=
  ⟨_, kron_unitary a b⟩

infixl:100 " ⊗ᵤ " => unitary_kron

@[simp, norm_cast]
theorem coe_unitary_kron (a : unitaryGroup α γ) (b : unitaryGroup β γ) :
  (↑(a ⊗ᵤ b) : Matrix (α × β) (α × β) γ)  = ↑a ⊗ₖ ↑b := by rfl

theorem unitary_row_inner {α : Type*} [CommRing α] [StarRing α]
    {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix.unitaryGroup n α) (i j : n) :
    ∑ k, A i k * star (A j k) = if i = j then 1 else 0 := by
  have h := congr_fun₂ (show A.val * star A.val = 1  by simp) i j
  simp only [mul_apply, star_apply, one_apply] at h
  exact h

@[simp]
theorem unitary_kron_mul (a a' : unitaryGroup α γ) (b b' : unitaryGroup β γ) :
  (a ⊗ᵤ b) * (a' ⊗ᵤ b')  = (a * a') ⊗ᵤ (b * b') := by
    ext
    push_cast
    simp only [mul_kronecker_mul]

@[simp]
theorem unitary_kron_one : (1 : unitaryGroup α γ) ⊗ᵤ (1 : unitaryGroup β γ) = 1 := by
  simp [unitary_kron]

@[simp]
theorem unitary_kron_inv (a : unitaryGroup α γ) (b : unitaryGroup β γ) :
  (a ⊗ᵤ b)⁻¹ = (a⁻¹ ⊗ᵤ b⁻¹) := inv_eq_of_mul_eq_one_left (by simp)

-- TBD: Choose name space
@[simps]
def rTensorHom : (unitaryGroup α γ) →* unitaryGroup (α × β) γ where
  toFun U := U ⊗ᵤ 1
  map_one' := by simp
  map_mul' := by simp
