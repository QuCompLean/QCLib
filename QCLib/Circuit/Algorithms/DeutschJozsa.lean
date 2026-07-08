/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani, George Afentakis
-/
import QCLib.Circuit.Gate.Qubit
import QCLib.Circuit.Hadamard

open Matrix

variable {n}
variable (f : Register n → Fin 2)

def oracle : 𝐔[Register n] :=
⟨diagonal (fun k ↦ (-1 : ℂ)^((f k) : ℕ)), by simp [Unitary.mem_iff, ← pow_add]⟩

noncomputable def DJ := HH n * oracle f * (HH n)⁻¹

theorem oracle_const (h : ∃ c, f = Function.const _ c) :
    oracle f = 1 ∨ oracle f = -1 := by
  obtain ⟨c, rfl⟩ := h
  fin_cases c <;> simp [UnitaryGroup.ext_iff,oracle, diagonal_apply, one_apply, Submonoid.smul_def]

theorem if_const (h : ∃ c, f = Function.const _ c) :
    ‖(DJ f • δ[(0 : Register n)]) (0 : Register n)‖ = 1 := by
  rcases oracle_const f h with h | h <;> simp [DJ, h, Submonoid.smul_def, basisVector_def]

open Classical in
def Function.IsBalanced {ι : Type} [Fintype ι] (f : ι → Fin 2) : Prop :=
  (Finset.univ.filter (fun i ↦ f i = 0)).card = (Finset.univ.filter (fun i ↦ f i = 1)).card

-- Maybe move this in QCLib.LinearAlgebra.UnitaryGroup.Basic? or .Action or .Lemmas?
--  Or do we have it already?
theorem Unitary.IsHermitian_inv {α : Type*} {m : Type*} [CommRing α] [StarRing α] [Fintype m]
    [DecidableEq m] {A : unitaryGroup m α} (h : Matrix.IsHermitian A.val) : A⁻¹ = A := by
  exact UnitaryGroup.ext A⁻¹ A fun i ↦ congrFun (congrFun h i)

lemma neg_one_pow_fin2 (a : Fin 2) : (-1 : ℂ) ^ (a : ℕ) = if a = 0 then 1 else -1 := by
  fin_cases a <;> simp

lemma balanced_sum_zero (h : Function.IsBalanced f) :  ∑ k, (-1 : ℂ) ^ ↑((f k) : ℕ) = 0 := by
  have h2 : ∀ x, ¬ f x = 0 ↔ f x = 1 := fun x => by fin_cases (f x) <;> grind
  simp only [neg_one_pow_fin2,Finset.sum_ite,Finset.sum_const]
  rw [Finset.filter_inj'.mpr (fun a _ ↦ h2 a), h]
  simp

theorem if_balanced (h : Function.IsBalanced f) : (DJ f • δ[(0 : Register n)]) 0 = (0 : ℂ) := by
  simp_rw [DJ, Unitary.IsHermitian_inv (HH_isHermitian n), ← smul_eq_mul, smul_assoc, HH_apply]
  rw [HadamardBasisVector, ← smul_assoc, smul_comm, smul_assoc, Finset.smul_sum]
  simp [oracle, basisVector_def, Finset.smul_sum, Matrix.unitaryGroup.smul_vec_def,
    HH_first_row_eq, ← Finset.mul_sum, balanced_sum_zero f h]

theorem deutsch_jozsa (f : Register n → Fin 2)
    (h : (∃ c, f = Function.const _ c) ∨ Function.IsBalanced f) :
    Function.IsBalanced f ↔ ‖(DJ f • δ[(0 : Register n)]) 0‖ = 0 := by
  grind [if_balanced f, norm_zero, if_const f]

theorem deutsch_jozsa' (f : Register n → Fin 2)
    (h : (∃ c, f = Function.const _ c) ∨ Function.IsBalanced f) :
    (∃ c, f = Function.const _ c) ↔ ‖(DJ f • δ[(0 : Register n)]) 0‖ = 1 := by
  grind [if_balanced f, norm_zero, if_const f]
