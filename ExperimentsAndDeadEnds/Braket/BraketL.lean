/-
Copyright (c) 2026 David Gross, Davood H. T. Therani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood H. T. Therani
-/

/-

# Dirac notation

Given an inner product space `E`, *Dirac notation* uses the symbol `|ψ⟩` ("ket")
for the linear map `ℂ → E` given by `s ↦ s • ψ` (a "homothety"). Dually, it uses
`⟨φ|` ("bra") for the adjoint of `|φ⟩`, i.e. the functional `ψ ↦ ⟪φ, ψ⟫`.

Further conventions:
* A vector `ψ` and the homothety `s ↦ s • ψ` are identified as required by context.
* The concatenation of bra's and ket's is interpreted as concatenation of linear maps.

Thus, for example:
* `⟨φ|ψ⟩` is the linear map `s ↦ ⟪φ, ψ⟫`, which is identified with `⟪φ, ψ⟫`.
* `|ψ⟩⟨φ|` is the rank-one operator `InnerProductSpace.rankOne ℂ ψ φ`.

Mathlib already contains a rich API for `InnerProductSpace.rankOne`.
Hence this file mainly adds some tooling around the edges: We set up custom notation,
register a coercion from homotheties to vectors, and add relevant lemmas to the
`simp` database.

TBD: Spell out intended simp normal form.

The `rankOne` API is stated for `ContinuousLinearMap`s, so this is what we'll use.
As a side-effect, this works in infinite dimensions. This does not seem to
introduce much friction...

...though `adjoint` wants to have a `CompleteSpace` instance. This dependency is
inherited from the Riesz representation theorem `InnerProductSpace.toDual`.  One
could define an `adjoint'` that doesn't require `[CompleteSpace]`, but would
only works on the linear span of `rankOne`s.  Probably not worth the bother.

## Main Definitions

None!

## Notation

* `|ψ⟩` for `rankOne ℂ ψ (1  : ℂ)`
* `⟨ψ|` for `rankOne ℂ (1  : ℂ) ψ`
* `|ψ⟩⟨φ|` for `rankOne ℂ ψ φ`

## Implementation notes

Concatenation of kets and bras is realized by `∘L`.

We don't define a custom notation for `⟨ψ|φ⟩`, as this would be too close to the existing `⟪ψ, φ⟫`.

## TODO

* Write a delaborator.

-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

open ContinuousLinearMap InnerProductSpace
open scoped InnerProduct ComplexInnerProductSpace

/-
Register additional `ext` lemmas for operators between normed `InnerProductSpace`s.
These are variants of `ext_inner_map`.

They facilitate the standard approach to prove equality of operators on `InnerProductSpace`s by
verifying that they have the same matrix elements.

TBD: Functionality currently depends on the order in which `ext_inner_map` and
the lemmas below are registered. Read up on how priorities work.
-/
section ext

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

@[ext]
lemma Qml.ext_inner_of_scalar {A B : ℂ →L[ℂ] F} (h : ∀ y, ⟪y, A 1⟫ = ⟪y, B 1⟫) : A = B := by
  ext
  exact ext_inner_left ℂ fun y ↦ h y

@[ext]
lemma Qml.ext_inner_to_scalar {A B : E →L[ℂ] ℂ} (h : ∀ x, ⟪1, A x⟫ = ⟪1, B x⟫) : A = B := by
  ext x
  simpa [RCLike.inner_apply] using h x

@[ext]
lemma Qml.ext_inner {A B : E →L[ℂ] F} (h : ∀ x y, ⟪y, A x⟫ = ⟪y, B x⟫) : A = B := by
  ext x
  exact ext_inner_left ℂ fun y ↦ h x y

end ext

namespace Braket

-- TBD: This uses `notation3`. Presumably, one should use more modern constructions.
-- This seem to require writing a `delaborator`.
scoped notation3 " ∣" ψ:90 "⟩⟨" φ:90 "∣ " => InnerProductSpace.rankOne ℂ ψ φ
scoped notation3:max "∣" ψ:90 "⟩ " => InnerProductSpace.rankOne ℂ ψ (1  : ℂ)
scoped notation3:max " ⟨" ψ:90 "∣" => InnerProductSpace.rankOne ℂ (1 : ℂ) ψ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

-- Coerce homotheties to the underlying vector
noncomputable instance : Coe (ℂ →L[ℂ] E) E := ⟨fun f ↦ f 1⟩

-- Add frequently used results to simp database
-- TBD: Think about simp normal form.
attribute [simp] ContinuousLinearMap.adjoint_toSpanSingleton
attribute [simp] ContinuousLinearMap.adjoint_innerSL_apply

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

-- `adjoint` wants a `ComnpleteSpace` instance
variable [CompleteSpace G] [CompleteSpace H]

-- Some corollaries
-- These need not remain here. I just want to see that the API works.

@[simp]
theorem bra_eq_ket_adjoint (ψ : G) : ⟨ψ∣ = ∣ψ⟩† := by
  simp only [rankOne_one_left_eq_innerSL]
  simp only [rankOne_one_right_eq_toSpanSingleton]
  simp only [adjoint_toSpanSingleton]

@[simp]
theorem bra_eq_ket_adjoint' (ψ : G) : ⟨ψ∣ = ∣ψ⟩† := by
  ext x
  simp only [rankOne_one_left_eq_innerSL]
  simp only [rankOne_one_right_eq_toSpanSingleton]
  simp only [adjoint_toSpanSingleton]

theorem ket_eq_bra_adjoint (ψ : G) : ∣ψ⟩ = ⟨ψ∣† := by simp

theorem braket_apply (ψ φ : E) : ⟨ψ∣ ∘L ∣φ⟩ = ⟪ψ, φ⟫ := by simp

theorem braket_eq_toSpanSingleton (ψ φ : E) : ⟨ψ∣ ∘L ∣φ⟩ = toSpanSingleton ℂ ⟪ψ, φ⟫ := by ext; simp

-- This fails witout the type hint.
theorem braket_self_norm_sq (ψ : E) : (⟨ψ∣ ∘L ∣ψ⟩ : ℂ) = ‖ψ‖^2 := by simp?

theorem ket_bra_adjoint_eq (ψ : G) (φ : H) : ∣ψ⟩⟨φ∣†  = ∣φ⟩⟨ψ∣ := by simp

theorem ket_bra_adjoint_eq' (ψ : G) (φ : H) : ∣ψ⟩⟨φ∣†  = ∣φ⟩⟨ψ∣ := by
  simp

theorem ket_bra_norm (ψ φ : E) : ‖∣ψ⟩⟨φ∣‖ = ‖ψ‖ * ‖φ‖ := norm_rankOne _ _

theorem ketbraket_eq_smul_ket (ψ φ : F) (χ : E) : ∣χ⟩ ∘L ⟨ψ∣ ∘L ∣φ⟩ = ⟪ψ, φ⟫ • ∣χ⟩ := by ext; simp

theorem ketbraketbra_eq_smul_ketbra (ψ : E) (φ α : F) (β : F) :
    ∣ψ⟩⟨φ∣ ∘L ∣α⟩⟨β∣ = ⟪φ, α⟫ • ∣ψ⟩⟨β∣ := by
  ext
  simp [inner_smul_right]
  grind -- linter is happpy with `grind` after non-squeezed `simp`

section Orthonormal

variable {ι : Type*} [Fintype ι]

example {v : ι → E} (hv : Orthonormal ℂ v) (x : ι → ℂ) (y : ι → ℂ) :
  (∑ i, (x i) • ⟨v i∣) ∘L (∑ j, (y j) • ∣v j⟩) = (∑ i, (x i) * (y i)) := by
  simp [Orthonormal.inner_right_fintype hv]

end Orthonormal

end Braket

