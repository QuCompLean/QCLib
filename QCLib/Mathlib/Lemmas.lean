/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Lie.OfAssociative -- `#min_imports` suggestions aren't really sensible
public import Mathlib.Analysis.Complex.Exponential
/-!

# Misc lemmas

In search of an appropriate home.

-/

@[expose] public section

/-- Delta functions on tuples factorize: `δ_{k}(l) = Π i, δ_{kᵢ}(lᵢ)` -/
theorem Pi.single_eq_prod {ι R : Type*} (κ : ι → Type*) [Fintype ι] [∀ i, DecidableEq (κ i)]
    [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R] [NeZero (1 : R)]
    (k l : (i : ι) → κ i) :
    Pi.single (M := fun _ ↦ R) k 1 l = ∏ i : ι, Pi.single (M := fun _ ↦ R) (k i) 1 (l i) := by
  simp only [Pi.single_apply]
  symm
  split_ifs with h
  · simp [h]
  · simp [Finset.prod_eq_zero_iff, Function.ne_iff.mp h]

-- Integer power version of `Finset.prod_pow_eq_pow_sum`. Does this exist somehwere?
theorem Finset.prod_zpow_eq_zpow_sum
    {ι G : Type} [CommGroup G] (s : Finset ι) (f : ι → ℤ) (a : G) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical exact Finset.induction_on s (by simp) (by simp_all [_root_.zpow_add])

theorem Finset.prod_zpow_eq_zpow_sum₀
    {ι M : Type} [CommGroupWithZero M] (s : Finset ι) (f : ι → ℤ) {a : M} (h : a ≠ 0) :
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical exact Finset.induction_on s (by simp) (by simp_all [_root_.zpow_add₀])

section noncommProd

/-- Two elements of a submonoid commute iff their coercions to the ambient monoid commute -/
@[simp]
theorem Submonoid.coe_commute_iff {M : Type*} [Monoid M] {S : Submonoid M} {a b : S} :
    (Commute (a : M) (b : M)) ↔ Commute a b := by
  refine ⟨(fun h ↦ ?_), (fun h ↦ ?_)⟩
  · simpa [commute_iff_eq, S.mul_def]
  · simpa [commute_iff_eq] using congrArg S.subtype h.eq

variable {F ι α β γ : Type*} (f : α → β)

open Finset

variable [Monoid β] [Monoid γ]

open scoped Function

@[simp]
theorem pairwise_commute_of_comp {α β γ F : Type*} [CommMonoid β] [Monoid γ]
    [FunLike F β γ] [MonoidHomClass F β γ] (s : Finset α) (f : α → β) (g : F) :
    (s : Set α).Pairwise (Commute on fun a ↦ g (f a)) :=
  (fun x _ y _ _ ↦ (Commute.all (f x) (f y)).map g)

/-- Write a `noncommProd` that factors through a commutative monoid as an ordinary product. -/
theorem noncommProd_comp_eq_prod {α β γ F : Type*} [CommMonoid β] [Monoid γ]
    [FunLike F β γ] [MonoidHomClass F β γ] (s : Finset α) (f : α → β) (g : F) :
    s.noncommProd (fun a ↦ g (f a)) (by simp) = g (s.prod f) := by
  simp [← map_noncommProd s f fun x _ y _ _ ↦ Commute.all (f x) (f y), noncommProd_eq_prod]

theorem noncommProd_lemma' (s : Finset α) (f : α → β) (comm : (s : Set α).Pairwise (Commute on f)) :
    Set.Pairwise {x | x ∈ s.toList.map f} Commute := by
  have h : { x | x ∈ s.val.map f } = {x | x ∈ s.toList.map f}  := by simp
  exact h ▸ noncommProd_lemma s f comm

@[simp, grind =]
theorem noncommprod_map_toList (s : Finset α) (comm) :
    (s.toList.map f).prod = s.noncommProd f comm := by
  simp only [Finset.noncommProd, ← Multiset.noncommProd_coe _ <| noncommProd_lemma' s f comm,
    ← Multiset.map_coe, Finset.coe_toList]

end noncommProd

section NegOne

-- TBD: C.f. `orderOf_neg_one`
-- Makes `simp` realize that `(-1 : ℂ) ≠ 1`
@[simp]
theorem _root_.Ring.neg_one_ne_one_of_char_zero_class {α : Type*} [Ring α] [CharZero α] :
    (-1 : α) ≠ 1 := by
  simp [Ring.neg_one_ne_one_of_char_ne_two]

end NegOne

open Complex in
theorem Complex.exp_nat_mul' (x : ℂ) (n : ℕ) :
    cexp (x * n) = cexp (x) ^ n := by
  simp [← Complex.exp_nat_mul, mul_comm]

end
