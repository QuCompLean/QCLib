/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import QCLib.Matrix.UnitaryGroup.Action
public import QCLib.Tactic.MatrixExpand

/-!
# Complex roots of unity

Misc defs and results relating to complex roots of unity, which came up when
working with the Pauli group and the quantum Fourier transform.

In many calculations that arise in these contexts, it's advantageous to bundle
the roots of unity as elements of `unitary ℂ`, e.g. to get access to its
well-behaved `zpow` instance.

This module is quite messy at the moment!

## Main definitions

* `ζ n` is `cexp (2 * π * I / n)`, a primitive `n`-th root of unity in `ℂ`
* `uζ n` the same, but bundled as an element of `unitary ℂ`

## Main results

TBD.

## Notation

Use left subscript of `u` for some common constants bundled as elements of `unitary ℂ`:
`ᵤ1`, `ᵤ-1`, `ᵤI`

## To do

Separate the results required for the QFT. Try to base them on more general
results in Mathlib / downstream repos.

Think about this entire approach.
-/

@[expose] public section

/-
# Roots of unity as `unitary ℂ`
-/

open Complex Real

variable (n : ℕ)

noncomputable def ζ (n : ℕ) := cexp (2 * π * I / n)

theorem ζ_def : ζ n = cexp (2 * π * I / n) := by rfl

variable [hnz : NeZero n]

theorem ζ_isPrimitiveRoot : IsPrimitiveRoot (ζ n) n :=
  isPrimitiveRoot_exp n hnz.ne

@[simp]
theorem orderOf_ζ : orderOf (ζ n) = n :=
  IsPrimitiveRoot.iff_orderOf.mp (ζ_isPrimitiveRoot n)

-- too complicated?
theorem ζ_mul_star_ζ_eq_one : ζ n * star (ζ n) = 1 := by
  have h := Complex.norm_eq_one_of_pow_eq_one (isPrimitiveRoot_exp n hnz.ne).pow_eq_one hnz.ne
  simp [RCLike.star_def, mul_conj, normSq_eq_norm_sq, h, ζ_def]

@[matrixExpand]
theorem ζ_mul_star_ζ_eq_one' : ζ n * (starRingEnd ℂ) (ζ n) = 1 := by
  apply ζ_mul_star_ζ_eq_one

lemma ζ_star : star (ζ n) = (ζ n)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [mul_comm, ζ_mul_star_ζ_eq_one]

section QFT

lemma ζ_pow_dvd (n m : ℕ) (hn : n ≠ 0) (hm : m ≠ 0) (hdvd : n ∣ m) :
    ζ m ^ (m / n) = ζ n := by
  obtain ⟨k, rfl⟩ := hdvd
  have hk : k ≠ 0 := by lia
  simp [hn, ζ_def, ← Complex.exp_nat_mul]
  ring_nf
  simp [mul_comm, ←mul_assoc, hk]

lemma ζ_pow_primepow (a k : ℕ) (ha : a ≠ 0) :
    ζ (a ^ (k + 1)) ^ (a ^ k) = ζ a := by
  simpa [pow_succ', ha] using
    ζ_pow_dvd a (a ^ (k + 1)) ha (pow_ne_zero (k + 1) ha) (dvd_pow_self a (by lia))

lemma ζ_pow_fin_rev (a n : ℕ) (u : Fin n) (ha : a ≠ 0) :
    ζ (a ^ (u + 1 : ℕ)) = ζ (a ^ n) ^ (a ^ (u.rev : ℕ)) := by
  have h :=
    (ζ_pow_dvd (a ^ (u + 1 : ℕ)) (a ^ n)
      (pow_ne_zero _ ha) (pow_ne_zero _ ha)
      (Nat.pow_dvd_pow _ (Nat.succ_le_of_lt u.is_lt)))
  rw [Nat.pow_div (by lia) (by lia)] at h
  simp_all

-- TBD: Feels too manual & complicated. Try to base on general results.
@[simp]
theorem ζ_sum_ortho {i j : Fin n} :
    ∑ x : Fin n, (ζ n) ^ ((i : ℤ) * x) * star (ζ n) ^ ((j : ℤ) * x)
      = n * ite (i = j) 1 0 := by
  simp_rw [ζ_star, inv_zpow', ← zpow_add₀ (a := (ζ n)) (by simp [ζ_def]),
    ← sub_eq_add_neg, ← mul_sub_right_distrib, zpow_mul, zpow_natCast, ← Finset.sum_range]
  by_cases hij : i = j
  · simp_all
  · rw [geom_sum_eq (x := (ζ n ^ (i - j : ℤ)))]
    · simp only [hij, ↓reduceIte, mul_zero, div_eq_zero_iff, ← zpow_natCast, zpow_comm]
      simp [zpow_natCast, (ζ_isPrimitiveRoot n).pow_eq_one]
    · exact fun h => (show (i : ℤ) ≠ j by grind)
        (sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs
          (((ζ_isPrimitiveRoot n).zpow_eq_one_iff_dvd (i - j)).mp h) (by omega)))

end QFT

noncomputable def uζ : (unitary ℂ) :=
    ⟨ζ n, by rw [mul_comm, ζ_mul_star_ζ_eq_one n], ζ_mul_star_ζ_eq_one n⟩

@[simp]
theorem coe_uζ : (uζ n : ℂ) = ζ n := rfl

@[simp]
theorem orderOf_uζ : orderOf (uζ n) = n := by
  simp [(orderOf_submonoid (uζ n)).symm]

notation "ᵤ1" => (1 : unitary ℂ)
notation "ᵤ-1" => (-1 : unitary ℂ)
notation "ᵤI" => (uζ 4)

theorem uζ_two_eq_neg_one : uζ 2 = (-1 : unitary ℂ) := by
  ext
  simp [ζ_def, field]
  ring_nf
  exact exp_pi_mul_I

theorem u_I_eq_I : ᵤI = (⟨I, by simp, by simp⟩ : unitary ℂ) := by
  ext
  simp [ζ_def, field]
  ring_nf
  grind [mul_comm, mul_assoc, exp_pi_div_two_mul_I]

set_option warn.sorry false in
-- `grind` above seems heavy-handed, but
-- `simp`, `ring_nf`, and `exp_pi_div_two_mul_I` all use different normal forms...
example (c : ℂ) : 2 * Real.pi / 4 * I = c := by
  ring_nf                               -- `↑π * I * (1 / 2)`
  simp                                  -- `↑π * I * 2⁻¹`
  have := isPrimitiveRoot_exp n hnz.ne  -- `cexp (2 * ↑π * I / ↑n`
  have := exp_pi_div_two_mul_I          -- `cexp (↑π / 2 * I) = I`
  sorry

-- needed?
@[simp]
theorem coe_u_I : (↑ᵤI : ℂ) = I := by simp only [u_I_eq_I]

@[simp]
theorem u_neg_one_zpow_two : ᵤ-1^(2 : ℤ) = ᵤ1 := by
  ext; push_cast; simp [field]

@[simp]
theorem orderOf_neg_one_eq_two : orderOf ᵤ-1 = 2 := by
  simp [← uζ_two_eq_neg_one]

@[simp]
theorem u_I_zpow_two : ᵤI^(2 : ℤ) = ᵤ-1 := by
  ext; push_cast; simp [u_I_eq_I, field]

@[simp]
theorem I_zpow_two : I^(2 : ℤ) = -1 := by
  simp only [fieldEq, I_sq]

@[simp]
theorem I_ne_zero : I ≠ 0 := by
  simp only [ne_eq, Complex.I_ne_zero, not_false_eq_true]

@[simp]
theorem uI_zpow_four : ᵤI^(4 : ℤ) = ᵤ1 := by
  ext; push_cast; simp [u_I_eq_I, field]

example : ¬(-1 : ℤ) = 1 := by simp only [Int.reduceNeg, reduceCtorEq, not_false_eq_true]

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]

/-- Use `ᵤ-1 • U` as simp normal form for the negation of a unitary. -/
 @[simp]
 theorem neg_unitary_eq_one_smul (U : unitaryGroup n ℂ) : -U = ᵤ-1 • U := by
   ext
   rw [Unitary.coe_neg, neg_apply, Unitary.coe_smul, smul_apply, Submonoid.smul_def,
    Unitary.coe_neg, OneMemClass.coe_one, smul_eq_mul, neg_mul, one_mul]
 -- with small imports, `simp [Submonoid.smul_def]` instead of the `rw` also works.
 -- But if Mathlib is imported, it istiming out trying to synthesize the
 -- (non-existing) `SMul ℂ (unitary n ℂ)`.
 -- Can one have a "shortcut to instance-doesn't-exist"?

theorem neg_vector_eq_one_smul {n : Type*} (v : n → ℂ) : ᵤ-1 • v = -v := by
  simp [Unitary.coe_neg, Submonoid.smul_def]

theorem neg_scalar_eq_one_smul (s : ℂ) : ᵤ-1 • s = -s := by
  simp [Unitary.coe_neg, Submonoid.smul_def]
