/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import QCLib.LinearAlgebra.UnitaryGroup.Permutation
public import QCLib.Circuit.Embed

/-!

TBD: Port.

-/

@[expose] public section

open Matrix.UnitaryGroup Equiv

/-- Rewrite a swap acting as a two-qubit gate in terms of a permutation of subsystems -/
theorem twoQubit_swap_eq_perm {n : ℕ} {i j : Fin n} (hneq : i ≠ j) :
    bipartite i j QubitSwap = permSubsystemsHom ℂ (Fin 2) (Equiv.swap i j) := by
  apply Matrix.UnitaryGroup.ext_smul_basis
  intro k
  simp only [twoQubit_apply_basis, swap_apply, Prod.swap_prod_mk, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, permSubsystemsHom_apply_apply,
    arrowCongrLeftHom_apply]
  congr 1
  ext a
  simp [arrowCongr_apply]
  grind

open List Fin

noncomputable def revCircuit (n : ℕ) : 𝐔[Register n] :=
  Finset.univ.noncommProd
    (fun i : Fin (n / 2) ↦ twoQubit Swap ⟨i, by lia⟩ ⟨n - (i + 1), by lia⟩ (by lia))
    (by
      simpa [twoQubit_swap_eq_perm,  ← revSwap_def] using
        fun i _ j _ hij => (Fin.pairwise_commute_on_revSwap
        (Set.mem_univ i) (Set.mem_univ j) (by simpa using hij)).map (permSubsystemsHom ℂ (Fin 2))
    )

theorem revCircuit_eq_revPermSubsystems (n : ℕ) :
    (revCircuit n) = permSubsystemsHom ℂ (Fin 2) revPerm := by
  simp_rw [revCircuit, ← noncommProd_revSwap_eq_revPerm,
    twoQubit_swap_eq_perm, Finset.map_noncommProd, revSwap_def]

@[simps! apply symm_apply]
def revRegister {n} : Equiv.Perm (Register n) := (arrowCongr revPerm (Equiv.refl (Fin 2)))

theorem revRegister_eq {n} (v : Register n) : revRegister v = fun i => v i.rev := rfl

open Function
theorem revRegister_comm_update {n} (v : Register n) (i m) :
  revRegister (update v i m) = update (revRegister v) i.rev m := by
  ext
  simp [update_apply]
  grind

theorem revRegister_comm_update' {n} (v : Register n) (i m) :
  revRegister (update v i.rev m) = update (revRegister v) i m := by
  ext
  simp [update_apply]

@[simp]
theorem revCircuit_apply {n : ℕ} (v : Register n) :
    revCircuit n • δ[v] = δ[revRegister v] := by
  simp [revCircuit_eq_revPermSubsystems, revRegister]

open scoped PiOuterProduct

@[simp]
theorem revCircuit_apply_prod {n : ℕ} (v : Register n) (f : Fin n → ℂ) :
    revCircuit n • (⨂ i, f i • δ[v i]) = ⨂ i, f i • δ[v i.rev] := by
  simp [piOuterProduct_smul_univ, smul_comm, ←basisVector_eq_prod, revRegister_eq]


-- -- TBD: Why is this `noncomputable`?
-- /-- Quantum circuit that swaps the `i`-th and the `n - (i+1)`-th qubits. -/
-- noncomputable def revCircuit (n : ℕ) : 𝐔[Register n] :=
--   ((finRange (n / 2)).map (fun i : Fin (n / 2) ↦
--       twoQubit Swap ⟨i, by lia⟩ ⟨n - (i + 1), by lia⟩ (by lia))).prod

-- theorem revCircuit_eq_revPermSubsystems (n : ℕ) :
--     (revCircuit n) = permSubsystemsHom ℂ (Fin 2) revPerm := by
--   simpa [revCircuit, twoQubit_swap_eq_perm, ← revSwap_def, prod_finRange_revSwap_eq_revPerm]
--     using List.prod_map_hom (List.finRange (n / 2)) revSwap (permSubsystemsHom ℂ (Fin 2))

-- @[simp]
-- theorem revCircuit_apply (n : ℕ) (v : Register n) :
--     revCircuit n • δ[v] = δ[(arrowCongr revPerm (Equiv.refl (Fin 2))) v] := by
--   simp [revCircuit_eq_revPermSubsystems]
