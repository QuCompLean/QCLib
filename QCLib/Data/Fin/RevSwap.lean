/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
`Fin.revPerm` is the "antitone involution" on `Fin n`, which maps `i ↦ n-(i+1)`.
Here, we introduce the transpositions `revSwap i`, which exchange just one
specifc `i` with `n-(i+1)`.

## Main definitions

* `revSwap i`: For `i : Fin (n/2)`, the equivalence that swaps the `i`th and the `n-(i+1)`th
  element of `Fin n`

## Main results

* `noncommProd_revSwap_eq_revPerm` the product of all `revSwap`s equals `revPerm`

## Implementation details

Several results depend on whether an element `i : Fin n` satisfies

- `(hlft : 2 * i + 1 < n)`, i.e. `i` lies in the initial half of `Fin n`,
- `(hmid : n = 2 * j + 1)`, i.e. `i` is the midpoint of `Fin n` (this can only occur if `n` is odd),
- `(hrgt : n < 2 * j + 1)`, i.e. `i` lies in the right half of `Fin n`.

The form of these hypotheses is chosen to match the cases produce by `lt_trichotomy n (2*j + 1)`.

Note: As `i` ranges over `Fin (n/2)`, the equivalences `revSwap i` generate a group isomorphic to
`ℤ₂^(n/2)`, though we do not prove that explicitly.
-/

@[expose] public section

open Equiv MulAction

theorem Equiv.swap_elem_stabilizer {α : Type*} [DecidableEq α]
    {i j k : α} (hi : k ≠ i) (hj : k ≠ j) : swap i j ∈ stabilizer (Perm α) k := by
  simp only [mem_stabilizer_iff, Perm.smul_def]
  grind

namespace Fin

variable {n : ℕ}

/-- Swap the `i`th and the `n - (i+1)`th element of `Fin n` -/
def revSwap (i : Fin (n / 2)) := swap (α := Fin n) ⟨i, by lia⟩ ⟨n - (i + 1), by lia⟩

theorem revSwap_def (i : Fin (n / 2)) : revSwap i = swap ⟨i, by lia⟩ ⟨n - (i + 1), by lia⟩ := rfl

@[simp]
theorem revSwap_apply_left (i : Fin n) (hlft : 2 * i + 1 < n) :
  revSwap ⟨i, by lia⟩ i = ⟨n - (i + 1), by lia⟩ := by simp [revSwap_def]

@[simp]
theorem revSwap_apply_right (i : Fin n) (hrgt : n < 2 * i + 1) :
    revSwap ⟨n - (i + 1), by lia⟩ i = ⟨n - (i + 1), by lia⟩ := by
  simp only [revSwap_def]
  grind

theorem commute_revSwap (i j : Fin (n / 2)) : Commute (revSwap i) (revSwap j) := by
  ext
  simp only [revSwap_def, Perm.mul_def, swap_comp_apply]
  grind

@[simp]
theorem pairwise_commute_on_revSwap {s : Set (Fin (n / 2))} :
    s.Pairwise (Function.onFun Commute revSwap) :=
  fun i _ j _ _ ↦ commute_revSwap i j

section StabilizerSubgroups

variable (i : Fin (n / 2)) (j : Fin n)

/-- `revSwap i` acts trivially on `j` if `j ≠ i, n-(i+1)` -/
theorem revSwap_elem_stabilizer (hlft : j ≠ ⟨i, by lia⟩) (hrgt : j ≠ ⟨n - (i + 1), by lia⟩) :
    revSwap i ∈ stabilizer _ j := by
  simp [revSwap_def, swap_elem_stabilizer hlft hrgt]

/-- `revSwap i` acts trivially on the midpoint of `Fin n`. Non-vacuous only for odd `n` -/
@[simp]
theorem revSwap_elem_stabilizer_mid (hmid : n = 2 * j + 1) : revSwap i ∈ stabilizer _ j := by
  simp only [revSwap, mem_stabilizer_iff, Perm.smul_def]
  grind

open Finset

/-- A term not containing `revSwap j` acts trivially on `j` -/
theorem prod_revSwap_elem_stabilizer_left (hlft : 2 * j + 1 < n) (s : Finset (Fin (n / 2))) :
    (s.erase ⟨j, by lia⟩).noncommProd revSwap (by simp) ∈ stabilizer _ j :=
  noncommProd_induction _ _ _ _ (fun a b ↦ Subgroup.mul_mem _) (one_mem _)
    (fun i hi ↦ revSwap_elem_stabilizer i j (by grind) (by grind))

/-- A term not containing `revSwap (n - (j + 1))` acts trivially on `j` -/
theorem prod_revSwap_elem_stabilizer_right (hrgt : n < 2 * j + 1) (s : Finset (Fin (n / 2))) :
    (s.erase ⟨n - (j + 1), by lia⟩).noncommProd revSwap (by simp) ∈ stabilizer _ j :=
  noncommProd_induction _ _ _ _ (fun a b ↦ Subgroup.mul_mem _) (one_mem _)
    (fun i hi ↦ revSwap_elem_stabilizer i j (by grind) (by grind))

/-- A product of `revSwap`s fixes the midpoint. Non-vacuous only for odd `n` -/
theorem prod_revSwap_elem_stabilizer_mid (hmid : n = 2 * j + 1) (s : Finset (Fin (n / 2))) :
    s.noncommProd revSwap (by simp) ∈ stabilizer _ j :=
  noncommProd_induction _ _ _ _ (fun _ _ ↦ Subgroup.mul_mem _) (one_mem _)
    (fun i _ ↦ revSwap_elem_stabilizer_mid i j hmid)

end StabilizerSubgroups

variable (n)

open Finset in
/-- The product of all `revSwap`s equals `revPerm` -/
theorem noncommProd_revSwap_eq_revPerm : univ.noncommProd revSwap (by simp) = revPerm (n := n) := by
  ext j
  rcases lt_trichotomy n (2*j + 1) with h | h | h
  · rw [← mul_noncommProd_erase _ (mem_univ ⟨n - (j + 1), by lia⟩)]
    have := prod_revSwap_elem_stabilizer_right j h univ
    simp_all
  · have := prod_revSwap_elem_stabilizer_mid j h univ
    simp_all
    grind
  · rw [← mul_noncommProd_erase _ (mem_univ ⟨j, by lia⟩)]
    have := prod_revSwap_elem_stabilizer_left j h univ
    simp_all

open List in
theorem prod_finRange_revSwap_eq_revPerm : ((finRange (n/2)).map revSwap).prod = revPerm := by
  simp_rw [← noncommProd_revSwap_eq_revPerm, ← toFinset_finRange,
    Finset.noncommProd_toFinset _ revSwap (by simp) (nodup_finRange (n/2))]

end Fin
