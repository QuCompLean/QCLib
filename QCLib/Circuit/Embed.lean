/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import QCLib.Circuit.Gate.Bipartite
public import QCLib.Logic.Equiv
public import QCLib.LinearAlgebra.OuterProduct


/-!

# Embedding unitary gates into larger systems

## Main Definitions

* `single i U` : The embedding of a unitary matrix `U : 𝐔ᶠ[k]` into `𝐔ᶠ[ι → k]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices.

* `bipartite i j U` : The embedding of a unitary matrix `U : 𝐔ᶠ[k × k]` into `𝐔ᶠ[ι → k]`
realized by acting with `U` on the `i`th and the `j`th index, and trivially on all other indices.

For the dependent case, use `single'` and `bipartite'`.

## Main results

TBD

-/

@[expose] public noncomputable section

open Unitary.EuclideanCLM OuterProduct Function PiOuterProduct EuclideanSpace Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {k : ι → Type*} [∀ i, DecidableEq (k i)] [∀ i, Fintype (k i)]

/-- The embedding of a unitary matrix `U : 𝐔[k i]` into `𝐔[Π i, k i]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices. -/
@[simps! coe]
def single' (i : ι) (U : 𝐔ᶠ[k i]) : 𝐔ᶠ[Π i, k i] :=
  reindexMonoidEquiv (Equiv.piSplitAt i k).symm (blockDiagonalStarMonoidHom (fun _ ↦ U))

/-- The embedding of a unitary matrix `U : 𝐔[k]` into `𝐔[ι → k]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices. -/
abbrev single {k : Type*} [DecidableEq k] [Fintype k] (i : ι) (U : 𝐔ᶠ[k]) :=
  single' (k := fun _ ↦ k) i U

theorem single_eq_prod (i : ι) (U : 𝐔ᶠ[k i]) :
    single' i U = ⨂ j, if h : j = i then h ▸ U else (1 : 𝐔ᶠ[k j]) := by
  apply unitaryGroupEquiv.symm.injective
  ext v a
  simp [blockDiagonal_apply, funext_iff]
  sorry
  -- simp only [single'_coe, submatrix_apply, blockDiagonal_apply, funext_iff,
  --   Subtype.forall, piKroneckerUnitary_apply]
  -- split_ifs with h
  -- · rw [Finset.prod_eq_single i] <;> aesop
  -- · obtain ⟨w, hw⟩ := not_forall.mp h
  --   rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp_all)]
