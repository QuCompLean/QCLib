/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Nat.Cast.Order.Ring
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!

# Results on `ℤ → Fin 2` coercions

In the context of the qubit Pauli group, it's convenient to interconvert
seamlessly between `ℤ` and `Fin 2`.

This file states a few defs and results in this context.

## Implementation notes

See warning below.
-/

@[expose] public section

-- Required for `ℤ → Fin n` coercions
-- These come with warnings, see docstring above
-- #check Fin.instAddMonoidWithOne
open scoped Fin.IntCast

-- TBD: Why is `NeZero` required?

@[coe]
def Fin.piIntCast {ι : Type*} {n : ℕ} [NeZero n] : (ι → ℤ) → (ι → Fin n) := fun v ↦ fun i ↦ ↑(v i)

@[simp]
theorem Even.intCast_fin_two {z : ℤ} (h : Even z) : (z : Fin 2) = 0 := by
  grind [Fin.val_intCast]

@[simp]
theorem Odd.intCast_fin_two {z : ℤ} (h : Odd z) : (z : Fin 2) = 1 := by
  grind [Fin.val_intCast]

-- TBD. Make this scoped.
instance {ι : Type*} {n : ℕ} [NeZero n] : Coe (ι → ℤ) (ι → Fin n) where
  coe := Fin.piIntCast

@[push_cast, simp]
theorem Fin.piIntCast_apply {ι : Type*} {n : ℕ} [NeZero n] (v : ι → ℤ) (i : ι) :
    (↑v : ι → Fin n) i = ↑(v i) := rfl

example {ι : Type*} {n : ℕ} [NeZero n] (v : ι → ℤ) (i : ι) :
    ((v : ι → Fin n) i).val = (v i % n).toNat := by simp

-- For scalars, this direction is generally available
@[coe]
def Int.piFinCast {ι : Type*} {n : ℕ} [NeZero n] : (ι → Fin n) → (ι → ℤ) := fun v ↦ fun i ↦ ↑(v i)

instance {ι : Type*} {n : ℕ} [NeZero n] : CoeHead (ι → Fin n) (ι → ℤ) where
  coe := Int.piFinCast

@[push_cast, simp]
theorem Int.piFinCast_apply {ι : Type*} {n : ℕ} [NeZero n] (v : ι → Fin n) (i : ι) :
    (↑v : ι → ℤ) i = ↑(v i) := rfl

example (n : ℕ) : ((n : ℤ).toNat) = n := Int.toNat_natCast n

example (n : ℕ) [NeZero n] (k : Fin n) : (Fin.ofNat n (k.toNat)) = k := by
  simp only [Fin.toNat_eq_val, Fin.ofNat_eq_cast, Fin.cast_val_eq_self]

@[simp]
theorem Fin.finCast_intCast_eq_self (n : ℕ) [NeZero n] (k : Fin n) : ((k : ℤ) : Fin n) = k := by
  simpa [Nat.cast_nonneg k] using Fin.intCast_def (n := n) (k : ℤ)

@[simp]
theorem Int.toFin_finCast {ι : Type*} {n : ℕ} [NeZero n] (v : ι → Fin n) :
    ((v : ι → ℤ) : ι → Fin n) = v := by
  refine funext (fun i ↦ ?_) -- TBD: `ext` picks wrong lemma?
  push_cast
  exact Fin.finCast_intCast_eq_self n (v i)
