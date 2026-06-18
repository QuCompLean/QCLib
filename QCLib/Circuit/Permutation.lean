/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import QCLib.LinearAlgebra.UnitaryGroup.Permutation
public import QCLib.Circuit.Embed
public import QCLib.Data.Fin.RevSwap

/-!

# Actions of permutations on `n` qubit systems

For now, this file only says that the "antitone" permutation `i ↦ n - (i + 1)`
of `Fin n` acting on subsytems has a circuit decompostion.

## To do

* Make independent of local dimension.
* Add more results.

-/

@[expose] public section

open Matrix.UnitaryGroup Equiv

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Rewrite a swap acting as a two-qudit gate in terms of a permutation of subsystems -/
theorem bipartite_swap_eq_perm {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    bipartite i j Swap h = permSubsystemsHom ℂ d (Equiv.swap i j) := by
  apply Matrix.UnitaryGroup.ext_smul_basis
  intro k
  simp only [bipartite_apply_basis, _root_.swap_apply_apply, Prod.swap_prod_mk, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
    permSubsystemsHom_apply_basis, arrowCongrLeftHom_apply]
  congr 1
  ext a
  simp
  grind

section RevCircuit

open List Fin

variable (d) in
noncomputable def revCircuit (n : ℕ) : 𝐔[Fin n → d] :=
  Finset.univ.noncommProd
    (fun i : Fin (n / 2) ↦ bipartite ⟨i, by lia⟩ ⟨n - (i + 1), by lia⟩ Swap)
    (by
      simp only [Finset.coe_univ, bipartite_swap_eq_perm, ← revSwap_def]
      intro i _ j _ hij
      exact (Fin.pairwise_commute_on_revSwap
        (Set.mem_univ i) (Set.mem_univ j) (by simpa using hij)).map (permSubsystemsHom ℂ d))

theorem revCircuit_eq_revPermSubsystems (n : ℕ) :
    (revCircuit d n) = permSubsystemsHom ℂ d revPerm := by
  simp_rw [revCircuit, ← noncommProd_revSwap_eq_revPerm,
    bipartite_swap_eq_perm, Finset.map_noncommProd, revSwap_def]

@[simps! apply symm_apply]
def revRegister {n} : Equiv.Perm (Fin n → d) := (arrowCongr revPerm (Equiv.refl d))

theorem revRegister_eq {n d} (v : Fin n → Fin d) : revRegister v = fun i ↦ v i.rev := rfl

open Function

theorem revRegister_comm_update {n d} (v : Fin n → Fin d) (i m) :
  revRegister (update v i m) = update (revRegister v) i.rev m := by
  ext
  simp [update_apply]
  grind

@[simp]
theorem revCircuit_apply {n : ℕ} (v : Fin n → d) :
    revCircuit d n • δ[v] = δ[revRegister v] := by
  simp [revCircuit_eq_revPermSubsystems, revRegister]

@[simp]
theorem revCircuit_involution {n d} :
    revCircuit (Fin d) n * revCircuit (Fin d) n = 1 := by
  apply ext_smul_basis
  intro i
  simp [← smul_eq_mul, revRegister_eq]


end RevCircuit
