/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.Algebra.Ring.Int.Parity

/-!

Some lemmas to reason about the order of elements in a `Monoid`.

This needs cleaning up.

-/

@[expose] public section

section OrderOf

/-
`IsPrimitiveRoot` seems to have large overlap with `orderOf`.
The former assumes `CommMonoid`, the latter just `Monoid`.
Stick with `orderOf` as primary API.
-/
-- #check IsPrimitiveRoot.iff_orderOf -- ` [CommMonoid M] : IsPrimitiveRoot ζ k ↔ orderOf ζ = k`


/-
The theorem below allows one to find the order of a root `y` of `x` given the order of `x`.

TBD: This should generalize to the case of an `e`-th root `y` of `x`, if every prime
factor of `e` is a prime factor of `orderOf x`.

TBD: This needs cleaning up. Also: Think about API.
-/

/-- If `x` has order `p^(k+1)` and `y` is a `p^l`-th root of `x`, then its order is `p^(l+k+1)` -/
theorem orderOf_prime_pow_root {M : Type*} [Monoid M] {p : ℕ} [hp : Fact p.Prime] {k l : ℕ}
    {x y : M} (hx : orderOf x = p ^ (k + 1)) (hr : y ^ (p ^ l) = x) :
    orderOf y = p ^ (l + k + 1) := by
  apply orderOf_eq_prime_pow
  · rw [pow_add, pow_mul, hr]
    -- this is ridiculous. clean up! add API if necessary.
    have := ((orderOf_eq_iff (Nat.pos_of_neZero (p ^ (k + 1)))).mp hx).2 (p ^ k)
    simpa using this (Nat.pow_lt_pow_succ hp.out.one_lt) (Nat.pos_of_neZero (p ^ k))
  · -- why can't i inline `this` in the `simpa` call?
    have := hr ▸ hx ▸ pow_orderOf_eq_one x
    simpa [← pow_mul, ← pow_add, ← add_assoc] using this

-- Saner-to-use API. Switch?
/-- If `x` has order `p^k` and `y` is a `p^l`-th root of `x`, then its order is `p^(l+k)` -/
theorem orderOf_prime_pow_root' {M : Type*} [Monoid M] {p : ℕ} [hp : Fact p.Prime] {k : ℕ}
    {x y : M} (hx : orderOf x = p ^ k) (hr : y ^ p = x) (hpos : 0 < k := by simp) :
    orderOf y = p ^ (k + 1) := by
  let k' := k - 1
  have : k = k' + 1 := by grind
  rw [this] at hx ⊢
  rw [show p = p ^ 1 by simp] at hr
  grind [orderOf_prime_pow_root hx hr]

example {M : Type*} [Group M] {ζ : M} {n : ℕ} (hord : orderOf ζ = n) (y z : ℤ) :
    ζ ^ y = ζ ^ z ↔ y ≡ z [ZMOD n] := hord ▸ zpow_eq_zpow_iff_modEq

-- TBD: remove?
-- TBD: Is this already somewhere in Mathlib? Maybe here?
-- #check Function.Periodic.lift
-- #check Function.Periodic.smul
-- #check AddSubgroup.zmultiples
--
/-- Formulas for elements of finite orbits. Does this exist? -/
theorem zpow_smul_eq_of_periodic {G α : Type*} [Group G] {x : G}
    {n : ℕ} (hpos : 0 < n) (hx : orderOf x = n)
    [SMul G α] {a : α} {f : ℤ → α} (h_period : ∀ z : ℤ, f z = f (z % n))
    (hfin : ∀ k : Fin n, x ^ (k : ℕ) • a = f k) : ∀ z : ℤ, x ^ z • a = f z := by
  intro z
  rw [← zpow_mod_orderOf x z, hx, h_period]
  have : 0 ≤ (z % ↑n) := Int.emod_nonneg z (by grind)
  rw [(Int.toNat_of_nonneg this).symm, zpow_natCast]
  have : (z % ↑n) < n := Int.emod_lt_of_pos z (by simp [hpos])
  simp only [hfin ⟨(z % n).toNat, by grind⟩]

/-
`grind` is good at solving `a % n = b % n`, but doesn't seem to understand the
notation `a ≡ b [ZMOD  n]`.

Also, does `Int.ModEq` have an `_iff` lemma?
-/
attribute [grind] Int.ModEq

end OrderOf

section Parity

@[simp]
theorem Even.zpow_of_sq
  {G : Type*} [Group G] {x : G} {q : ℤ} (h : Even q) (hsq : x * x = 1) : x ^ q = 1 := by
  obtain ⟨_, rfl⟩ := even_iff_exists_two_mul.mp h
  rw [_root_.zpow_mul, zpow_two, hsq, _root_.one_zpow]

@[simp]
theorem Odd.zpow_of_sq
  {G : Type*} [Group G] {x : G} {q : ℤ} (h : Odd q) (hsq : x * x = 1) : x ^ q = x := by
  obtain ⟨_, rfl⟩ := odd_iff_exists_bit1.mp h
  rw [_root_.zpow_add, _root_.zpow_mul, zpow_two, hsq, _root_.one_zpow, zpow_one, one_mul]

@[simp]
theorem Even.pow_of_sq
  {G : Type*} [Group G] {x : G} {q : ℕ} (h : Even q) (hsq : x * x = 1) : x ^ q = 1 :=
  zpow_natCast x q ▸ ((Int.even_coe_nat q).mpr h).zpow_of_sq hsq

@[simp]
theorem Odd.pow_of_sq
  {G : Type*} [Group G] {x : G} {q : ℕ} (h : Odd q) (hsq : x * x = 1) : x ^ q = x :=
  zpow_natCast x q ▸ ((Int.odd_coe_nat q).mpr h).zpow_of_sq hsq

end Parity
