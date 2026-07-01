module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring.RingNF
public import QCLib.LinearAlgebra.UnitaryGroup.RootsOfUnity


@[expose] public section

variable {n d : ℕ}

open Equiv

namespace Fin

/-- Equivalence between `Fin n → Fin d` and `Fin (d ^ n)` using big-endian order. -/
def ofDigitsBE : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (piCongrLeft' _ revPerm).trans finFunctionFinEquiv

theorem ofDigitsBE_val_apply (f : Fin n → Fin d) :
    ofDigitsBE f = ∑ i : Fin n, (f i.rev) * d ^ (i : ℕ):= by
  simp [ofDigitsBE, piCongrLeft', finFunctionFinEquiv]

theorem ofDigitsBE_apply_reindex [NeZero d] (v : Fin n → Fin d) :
    ((ofDigitsBE v) : ℕ) = ∑ i : Fin n, (v i : ℕ) * d ^ (n - 1 - i : ℕ) := by
  rw [ofDigitsBE_val_apply]
  apply Finset.sum_equiv Fin.revPerm (by simp) (fun i _ => ?_)
  simp only [revPerm_apply, val_rev, mul_eq_mul_left_iff, val_eq_zero_iff]
  left
  congr
  lia

/-- Equivalence between `Fin n → Fin d` and `Fin (d ^ n)` using little-endian order. -/
@[simps! -isSimp apply symm_apply]
def ofDigits : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  finFunctionFinEquiv

@[simp]
theorem ofDigitsBE_rev_eq_ofDigits (f : Fin n → Fin d) :
    ofDigitsBE (fun i => f i.rev) = ofDigits f := by
  ext
  simp [ofDigitsBE_val_apply, ofDigits_apply]

lemma ofDigits_val_rec (g : Fin (n + 1) → Fin d) :
    (ofDigits g : ℕ) = (g 0 : ℕ) + d * (ofDigits (Fin.tail g) : ℕ) := by
  simp [ofDigits_apply, Fin.sum_univ_succ, Fin.tail, Finset.mul_sum]
  grind

lemma ofDigitsBE_val_rec (f : Fin (n + 1) → Fin d) :
    (ofDigitsBE f : ℕ) = (f 0 : ℕ) * d ^ n + (ofDigitsBE (Fin.tail f) : ℕ) := by
  simp [ofDigitsBE_val_apply, Fin.sum_univ_castSucc, add_comm, rev_castSucc, Fin.tail]

theorem ofDigitsBE_ofDigits_rec (f g : Fin (n + 1) → Fin d) :
    (ofDigitsBE f : ℕ) * (ofDigits g : ℕ) =
      (ofDigitsBE (tail f) : ℕ) * (g 0 : ℕ)
      + (f 0 : ℕ) * (g 0 : ℕ) * d ^ n
      + d * (ofDigitsBE (tail f) : ℕ) * (ofDigits (tail g) : ℕ)
      + (f 0 : ℕ) * d ^ (n + 1) * (ofDigits (tail g) : ℕ) := by
  simp [ofDigits_val_rec, ofDigitsBE_val_rec]
  ring
