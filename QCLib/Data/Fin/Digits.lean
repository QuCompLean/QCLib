module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.Ring.RingNF
public import QCLib.LinearAlgebra.UnitaryGroup.RootsOfUnity


@[expose] public section

variable {n d : ℕ}

open Equiv

namespace Fin

-- Put in `Function` namespace to allow for dot notation
/-- Equivalence between `Fin n → Fin d` and `Fin (d ^ n)` using big-endian order. -/
def _root_.Function.ofDigitsBE : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (piCongrLeft' _ revPerm).trans finFunctionFinEquiv

theorem val_ofDigitsBE_apply (f : Fin n → Fin d) :
    (f.ofDigitsBE : ℕ) = ∑ i : Fin n, (f i.rev) * d ^ (i : ℕ):= by
  simp [Function.ofDigitsBE, piCongrLeft', finFunctionFinEquiv]

theorem val_ofDigitsBE_apply_reindex (v : Fin n → Fin d) :
    (v.ofDigitsBE : ℕ) = ∑ i : Fin n, v i * d ^ (n - 1 - i) := by
  rw [val_ofDigitsBE_apply]
  apply Finset.sum_equiv Fin.revPerm (by simp) (fun i _ ↦ ?_)
  simp only [revPerm_apply, val_rev, mul_eq_mul_left_iff]
  grind

/-- Equivalence between `Fin n → Fin d` and `Fin (d ^ n)` using little-endian order. -/
@[simps! -isSimp apply symm_apply]
def _root_.Function.ofDigits : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  finFunctionFinEquiv

@[simp]
theorem ofDigitsBE_rev_eq_ofDigits (f : Fin n → Fin d) :
    (fun i ↦ f i.rev).ofDigitsBE = f.ofDigits := by
  ext
  simp [val_ofDigitsBE_apply, Function.ofDigits_apply]

lemma val_ofDigits_rec (g : Fin (n + 1) → Fin d) :
    (g.ofDigits : ℕ) = (g 0 : ℕ) + (Fin.tail g).ofDigits * d := by
  simp [Function.ofDigits_apply, Fin.sum_univ_succ, Fin.tail, Finset.sum_mul]
  grind

lemma val_ofDigitsBE_rec (f : Fin (n + 1) → Fin d) :
    f.ofDigitsBE = (f 0 : ℕ) * d ^ n + (Fin.tail f).ofDigitsBE := by
  simp [val_ofDigitsBE_apply, Fin.sum_univ_castSucc, add_comm, rev_castSucc, Fin.tail]

theorem ofDigitsBE_ofDigits_rec (f g : Fin (n + 1) → Fin d) :
    (f.ofDigitsBE : ℕ) * g.ofDigits =
      (tail f).ofDigitsBE * g 0
      + (f 0) * (g 0) * d ^ n
      + (tail f).ofDigitsBE * (tail g).ofDigits * d
      + (f 0) * (tail g).ofDigits * d ^ (n + 1) := by
  simp [val_ofDigits_rec, val_ofDigitsBE_rec]
  ring

end Fin
