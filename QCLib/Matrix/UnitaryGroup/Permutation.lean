/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import QCLib.Matrix.UnitaryGroup.Action
public import QCLib.Matrix.UnitaryGroup.Basic
public import QCLib.Circuit.StdBasis

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

-- TBD: Move stuff below to the quantum gates folder

-- open Matrix.UnitaryGroup
--
-- -- TBD: Re-define `Swap` to make this simpler? What about introducing a
-- -- `twoQubit'` that takes `Fin 2 → Fin 2` as a model rather than `Fin 2 × Fin 2`?
-- /-- Rewrite a swap acting as a two-qubit gate in terms of a permutation of subsystems -/
-- theorem twoQubit_swap_eq_perm {n : ℕ} {i j : Fin n} (hneq : j ≠ i) :
--     twoQubit Swap i j hneq = permSubsystemsHom ℂ (Fin 2) (Equiv.swap i j) := by
--   apply Register.Matrix.UnitaryGroup.ext_smul_basis
--   intro k
--   simp only [twoQubit_apply_basis, swap_apply, Prod.swap_prod_mk, ite_smul, one_smul, zero_smul,
--     Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, permSubsystemsHom_apply_apply,
--     arrowCongrLeftHom_apply]
--   congr 1
--   ext a
--   simp [arrowCongr_apply]
--   grind
--
-- open List Fin
--
-- noncomputable def revCircuit (n : ℕ) : 𝐔[Register n] :=
--   Finset.univ.noncommProd
--     (fun i : Fin (n / 2) ↦ twoQubit Swap ⟨i, by lia⟩ ⟨n - (i + 1), by lia⟩ (by lia))
--     (by
--       simpa [twoQubit_swap_eq_perm,  ← revSwap_def] using
--         fun i _ j _ hij => (Fin.pairwise_commute_on_revSwap
--         (Set.mem_univ i) (Set.mem_univ j) (by simpa using hij)).map (permSubsystemsHom ℂ (Fin 2))
--     )
--
-- theorem revCircuit_eq_revPermSubsystems (n : ℕ) :
--     (revCircuit n) = permSubsystemsHom ℂ (Fin 2) revPerm := by
--   simp_rw [revCircuit, ← noncommProd_revSwap_eq_revPerm,
--     twoQubit_swap_eq_perm, Finset.map_noncommProd, revSwap_def]
--
-- @[simps! apply symm_apply]
-- def revRegister {n} : Equiv.Perm (Register n) := (arrowCongr revPerm (Equiv.refl (Fin 2)))
--
-- theorem revRegister_eq {n} (v : Register n) : revRegister v = fun i => v i.rev := rfl
--
-- open Function
-- theorem revRegister_comm_update {n} (v : Register n) (i m) :
--   revRegister (update v i m) = update (revRegister v) i.rev m := by
--   ext
--   simp [update_apply]
--   grind
--
-- theorem revRegister_comm_update' {n} (v : Register n) (i m) :
--   revRegister (update v i.rev m) = update (revRegister v) i m := by
--   ext
--   simp [update_apply]
--
-- @[simp]
-- theorem revCircuit_apply {n : ℕ} (v : Register n) :
--     revCircuit n • δ[v] = δ[revRegister v] := by
--   simp [revCircuit_eq_revPermSubsystems, revRegister]
--
-- @[simp]
-- theorem revCircuit_apply_prod {n : ℕ} (v : Register n) (f : Fin n → ℂ) :
--     revCircuit n • (⨂ᵥ i, f i • δ[v i]) = ⨂ᵥ i, f i • δ[v i.rev] := by
--   simp [piTensorProduct_smul_univ, smul_comm, ←Register.basisVector_eq_prod, revRegister_eq]
--
--
-- -- -- TBD: Why is this `noncomputable`?
-- -- /-- Quantum circuit that swaps the `i`-th and the `n - (i+1)`-th qubits. -/
-- -- noncomputable def revCircuit (n : ℕ) : 𝐔[Register n] :=
-- --   ((finRange (n / 2)).map (fun i : Fin (n / 2) ↦
-- --       twoQubit Swap ⟨i, by lia⟩ ⟨n - (i + 1), by lia⟩ (by lia))).prod
--
-- -- theorem revCircuit_eq_revPermSubsystems (n : ℕ) :
-- --     (revCircuit n) = permSubsystemsHom ℂ (Fin 2) revPerm := by
-- --   simpa [revCircuit, twoQubit_swap_eq_perm, ← revSwap_def, prod_finRange_revSwap_eq_revPerm]
-- --     using List.prod_map_hom (List.finRange (n / 2)) revSwap (permSubsystemsHom ℂ (Fin 2))
--
-- -- @[simp]
-- -- theorem revCircuit_apply (n : ℕ) (v : Register n) :
-- --     revCircuit n • δ[v] = δ[(arrowCongr revPerm (Equiv.refl (Fin 2))) v] := by
-- --   simp [revCircuit_eq_revPermSubsystems]

end
