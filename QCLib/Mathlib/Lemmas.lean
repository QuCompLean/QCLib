/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Lie.OfAssociative

/-!

# Misc lemmas

In search of an appropriate home.

-/

@[expose] public section

section noncommProd

@[simp]
theorem Submonoid.coe_commute_iff {M : Type*} [Monoid M] {S : Submonoid M} {a b : S} :
    (Commute (a : M) (b : M)) ↔ Commute a b := by
  refine ⟨(fun h ↦ ?_), (fun h ↦ ?_)⟩
  · simpa [commute_iff_eq, S.mul_def]
  · simpa [commute_iff_eq] using congrArg S.subtype h.eq

variable {F ι α β γ : Type*} (f : α → β)

open Finset

variable [Monoid β] [Monoid γ]

/-- Write a `noncommProd` that factors through a commutative monoid as an ordinary product. -/
theorem noncommProd_comp_eq_prod {α β γ F : Type*} [Monoid α] [CommMonoid β] [Monoid γ]
    [FunLike F β γ] [MonoidHomClass F β γ] (s : Finset α) (f : α → β) (g : F) :
    s.noncommProd (g ∘ f) (fun x _ y _ _ ↦ (Commute.all (f x) (f y)).map g) = g (s.prod f) := by
  simp [← map_noncommProd s f fun x _ y _ _ ↦ Commute.all (f x) (f y), noncommProd_eq_prod]

open scoped Function in
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

end
