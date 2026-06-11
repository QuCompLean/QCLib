module

public import Mathlib.Analysis.Fourier.ZMod

@[expose] public section

open Complex Real AddChar Fin.CommRing

variable {n : ℕ} [hn : NeZero n]

namespace Fin

section stdAddChar

/-- The additive character from `Fin n` to `ℂ`, sending `x : Fin n` to `exp (2 * π * I * x / n)`. -/
noncomputable def stdAddChar : AddChar (Fin n) ℂ :=
  ZMod.stdAddChar.compAddMonoidHom (ZMod.finEquiv n).toAddEquiv.toAddMonoidHom

notation3 "ζ(" x ")" => stdAddChar x
notation3 "ζ[" n "]" => stdAddChar (1 : Fin n)

-- TBD : Is there anyway to prove it without defeq abuse?
theorem stdAddChar_apply (x : Fin n) : ζ(x) = cexp (2 * π * I * x / n) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  simp [stdAddChar, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

lemma injective_stdAddChar : Function.Injective (stdAddChar : AddChar (Fin n) ℂ) := by
  simpa [stdAddChar] using ZMod.injective_stdAddChar

theorem isPrimitive_stdAddChar : (stdAddChar (n := n)).IsPrimitive := by
  intro a ha heq
  apply ha
  apply Fin.injective_stdAddChar
  simpa using AddChar.ext_iff.mp heq 1

@[simp]
theorem stdAddChar_orth (i j : Fin n) :
    ∑ x, ζ(i * x) * (starRingEnd ℂ) ζ(j * x) = ite (i = j) n 0 := by
  simp [← inv_apply_eq_conj, ← inv_apply', ← map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, mul_comm,
    AddChar.sum_mulShift _ isPrimitive_stdAddChar, sub_eq_zero]

theorem stdAddChar_ne_zero (x : Fin n) : ζ(x) ≠ 0 := by
  simp [stdAddChar_apply]

@[simp]
theorem stdAddChar_mul_self_conj (x : Fin n) :
    ζ(x) * (starRingEnd ℂ) ζ(x) = 1 := by
  simp [← map_neg_eq_conj, ← map_add_eq_mul]

theorem stdAddChar_isPrimitiveRoot : IsPrimitiveRoot ζ[n] n := by
  by_cases h : n = 1
  · subst h; simp
  · simp_rw [stdAddChar_apply, show ((1 : Fin n) : ℕ) = 1 by simp [Nat.one_mod_eq_one, h],
      Nat.cast_one, mul_one, isPrimitiveRoot_exp n (NeZero.ne n)]

@[simp]
theorem orderOf_stdAddChar : orderOf ζ[n] = n :=
  IsPrimitiveRoot.iff_orderOf.mp stdAddChar_isPrimitiveRoot


namespace pow

@[instance_reducible]
def instComplexPowFin : HPow ℂ (Fin n) ℂ where
  hPow a b := a ^ (b : ℕ)

attribute [scoped instance] instComplexPowFin

omit hn in
@[simp]
theorem cpow_fin_def (a : ℂ) (b : Fin n) : a ^ b = a ^ (b : ℕ) := rfl

-- TBD: remove defeq abuse
theorem stdAddChar_pow (n) (a : ℕ)
    [ha : NeZero a] (x : Fin (a ^ n)) (h : 2 ≤ a := by decide) :
    ζ[a ^ n] ^ x = ζ(x) := by
  cases n with
  | zero =>
    simp_rw [stdAddChar_apply]
    simp [show x = 1 by lia]
    rfl
  | succ n =>
    simp [stdAddChar_apply, ← Complex.exp_nat_mul, mul_comm,
      show 1 % a ^ (n + 1) = 1 by simp [Nat.one_mod_eq_one]; lia]
    ring_nf

end pow


end stdAddChar

noncomputable def stdAddCharUnitary : AddChar (Fin n) (unitary ℂ) :=
  AddChar.toMonoidHomEquiv.symm <|
    (stdAddChar.toMonoidHom).codRestrict (unitary ℂ)
      (by simp [Unitary.mem_iff_self_mul_star] )

notation "uζ("x")" => stdAddCharUnitary x
notation "uζ["n"]" => stdAddCharUnitary (1 : Fin n)
notation "ᵤ1" => (1 : unitary ℂ)
notation "ᵤ-1" => (-1 : unitary ℂ)
notation "ᵤI" => uζ[4]

theorem stdAddCharUnitary_apply (x : Fin n) : uζ(x) = cexp (2 * π * I * x / n) := by
  simp [stdAddCharUnitary, stdAddChar_apply]

@[simp]
theorem orderOf_stdAddCharUnitary : orderOf uζ[n] = n := by
  rw [(orderOf_submonoid (uζ[n])).symm]
  simp [stdAddCharUnitary]

theorem stdAddCharUnitar_two_eq_neg_one : uζ[2] = (-1 : unitary ℂ) := by
  ext
  simp [stdAddCharUnitary_apply]
  ring_nf
  exact exp_pi_mul_I

end Fin

open Fin

theorem u_I_eq_I : ᵤI = (⟨I, by simp, by simp⟩ : unitary ℂ) := by
  ext
  simp [stdAddCharUnitary_apply]
  ring_nf
  grind [mul_comm, mul_assoc, exp_pi_div_two_mul_I]

set_option warn.sorry false in
-- `grind` above seems heavy-handed, but
-- `simp`, `ring_nf`, and `exp_pi_div_two_mul_I` all use different normal forms...
example (c : ℂ) : 2 * Real.pi / 4 * I = c := by
  ring_nf                               -- `↑π * I * (1 / 2)`
  simp                                  -- `↑π * I * 2⁻¹`
  have := isPrimitiveRoot_exp n hn.ne  -- `cexp (2 * ↑π * I / ↑n`
  have := exp_pi_div_two_mul_I          -- `cexp (↑π / 2 * I) = I`
  sorry

@[simp]
theorem u_neg_one_zpow_two : ᵤ-1^(2 : ℤ) = ᵤ1 := by
  ext; push_cast; simp [field]

@[simp]
theorem orderOf_neg_one_eq_two : orderOf ᵤ-1 = 2 := by
  simp [← stdAddCharUnitar_two_eq_neg_one]

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
