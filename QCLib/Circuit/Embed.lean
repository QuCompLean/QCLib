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

open Unitary.EuclideanCLM OuterProduct
  Function PiOuterProduct Matrix Equiv

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {k : ι → Type*} [∀ i, DecidableEq (k i)] [∀ i, Fintype (k i)]

section single

/-- The embedding of a unitary matrix `U : 𝐔ᶠ[k i]` into `𝐔ᶠ[Π i, k i]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices. -/
@[simps! coe]
def single' (i : ι) (U : 𝐔ᶠ[k i]) : 𝐔ᶠ[Π i, k i] :=
  reindexMonoidEquiv (piSplitAt i k).symm (blockDiagonalStarMonoidHom (fun _ ↦ U))

/-- The embedding of a unitary matrix `U : 𝐔ᶠ[k]` into `𝐔ᶠ[ι → k]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices. -/
abbrev single {k : Type*} [DecidableEq k] [Fintype k] (i : ι) (U : 𝐔ᶠ[k]) :=
  single' (k := fun _ ↦ k) i U

theorem single_eq_prod (i : ι) (U : 𝐔ᶠ[k i]) :
    single' i U = ⨂ j, if h : j = i then h ▸ U else (1 : 𝐔ᶠ[k j]) := by
  apply unitaryGroupEquiv.symm.injective
  ext
  simp only [StarMulEquiv.coe_toMulEquiv, unitaryGroupEquiv_symm_apply, Subtype.map_coe,
    single'_coe, StarMulEquiv.toStarMonoidHom_coe, StarMulEquiv.ofClass_symm_apply,
    EquivLike.inv_apply_apply, submatrix_apply, piSplitAt_apply, ne_eq, blockDiagonal_apply,
    funext_iff, Subtype.forall, piTprod_coe, apply_dite, OneMemClass.coe_one,
     EuclideanCLM.piTprod_def, piKronecker_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single i] <;> aesop
  · obtain ⟨w, hw⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp_all)]

example {k : Type*} [DecidableEq k] [Fintype k] (i : ι) (U : 𝐔ᶠ[k]) :
    single i U = ⨂ j, if j = i then U else 1 := by
  simp [single_eq_prod]

attribute [simp] mulVec_eq_sum blockDiagonal_apply

@[simp]
theorem single_one (i : ι) : single' i (1 : 𝐔ᶠ[k i]) = 1 := by
  ext
  simp [one_apply, ← ite_and]

theorem single'_reindexMonoidEquiv {k' : ι → Type*} [∀ i, DecidableEq (k' i)] [∀ i, Fintype (k' i)]
    (e : ∀ i, k i ≃ k' i) (i : ι) (U : 𝐔ᶠ[k i]) :
    single' i (reindexMonoidEquiv (e i) U) =
      reindexMonoidEquiv (piCongrRight e) (single' i U) := by
  ext
  simp [funext_iff, Unitary.EuclideanCLM.reindexMonoidEquiv]

theorem single_reindexMonoidEquiv {k k' : Type*} [DecidableEq k] [DecidableEq k']
    [Fintype k] [Fintype k'] (e : k ≃ k') (i : ι) (U : 𝐔ᶠ[k]) :
    single i (reindexMonoidEquiv e U) =
    Unitary.EuclideanCLM.reindexMonoidEquiv (piCongrRight (fun _ : ι ↦ e)) (single i U) := by
  simp [← single'_reindexMonoidEquiv]

theorem single_diagonal (i : ι) (d : k i → unitary ℂ) :
    single' i (diagonalMonoidHom d) = diagonalMonoidHom (fun x ↦ d (x i)) := by
  ext
  simp [diagonalMonoidHom_coe, diagonal_apply]

theorem single_apply_basis (v : Π i, k i) (i : ι) (U : 𝐔ᶠ[k i]) :
    single' i U δ[v] =
      ∑ w, (U δ[v i]) w • δ[update v i w] := by
  ext x
  simp only [single'_coe, ofLp_toEuclideanCLM, mulVec_eq_sum, basisVector_apply,
    transpose_submatrix, blockDiagonal_transpose, op_smul_eq_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_apply, WithLp.ofLp_sum, WithLp.ofLp_smul, Pi.smul_apply, eq_update_iff, ne_eq,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_ite v (by simp_all)]
  simp_all [ite_and, funext_iff, toEuclideanCLM_symm_apply]
  grind

-- These simps do not commute ... find a better api
theorem single_apply_basis' (v : Π i, k i) (i : ι) (U : 𝐔ᶠ[k i]) :
    single' i U δ[v] = EuclideanSpace.piSplitAt i
      ((U δ[v i]) ⨂ δ[fun a : {j // j ≠ i} => v a]) := by
  ext
  simp [-single'_coe, single_apply_basis, eq_update_iff, ite_and]
  simp [funext_iff]

@[simp]
theorem single_single_commute {i j : ι} (h : i ≠ j) (U : 𝐔ᶠ[k i]) (V : 𝐔ᶠ[k j]) :
    Commute (single' i U) (single' j V) := by
  simp only [single_eq_prod, commute_iff_eq, mul_piTprod_mul]
  congr
  grind

-- The API doesn't naturally close this goal,
-- in fact, it produces a complicated goal that is hard to distangle.
theorem single_mul (i : ι) (U V : 𝐔ᶠ[k i]) :
    single' i (U * V) = single' i U * single' i V := by
  ext
  simp [← blockDiagonal_mul, ← map_mul]

@[simp]
theorem pairwise_commute_single (f : Π i, 𝐔ᶠ[k i]) (s : Set ι) :
    s.Pairwise (Function.onFun Commute (fun i ↦ single' i (f i))) :=
  (fun x _ y _ hneq ↦ single_single_commute hneq (f x) (f y))

-- TBD : Generalize it to dependent case
theorem noncommProd_single {k : Type*} [DecidableEq k] [Fintype k] (f : ι → 𝐔ᶠ[k]) (s : Finset ι) :
    s.noncommProd (fun i ↦ single i (f i)) (by simp) = ⨂ i, if (i ∈ s) then f i else 1 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha IH =>
    have (i : ι) : (if i = a ∨ i ∈ s then f i else 1) =
        (if i = a then f a else 1) * (if i ∈ s then f i else 1) := by grind
    simp_rw [Finset.noncommProd_cons, IH, Finset.cons_eq_insert, Finset.mem_insert, this,
      ← mul_piTprod_mul, single_eq_prod]
    simp

theorem noncommProd_single_univ {k : Type*} [DecidableEq k] [Fintype k] (f : ι → 𝐔ᶠ[k]) :
    Finset.noncommProd Finset.univ (fun i ↦ single i (f i)) (by simp) = ⨂ i, f i := by
  simp [noncommProd_single]

end single

section bipartite

-- TBD: Revisit argument order
/-- The embedding of a unitary matrix `U : U[k i × k j]` into `𝐔[Π i, k i]`
realized by acting with `U` on the `i`th and the `j`th index, and trivially on
all other indices. -/
@[simps!]
def bipartite' (i j : ι) (U : 𝐔ᶠ[k i × k j]) (h : i ≠ j := by grind) : 𝐔ᶠ[Π i, k i] :=
  reindexMonoidEquiv (Equiv.piSplitAtPair i j h.symm).symm
    <| blockDiagonalStarMonoidHom (fun _ ↦ U)

/-- `Matrix.UnitaryGroup.bipartite'` bundled as a monoid homomorphism. -/
def bipartiteMonoidHom' (i j : ι) (h : i ≠ j := by grind) : 𝐔ᶠ[k i × k j] →* 𝐔ᶠ[Π i, k i] :=
  (Unitary.EuclideanCLM.reindexMonoidEquiv (Equiv.piSplitAtPair i j h.symm).symm).toMonoidHom.comp
    <| blockDiagonalStarMonoidHom.toMonoidHom.comp <|
    Pi.monoidHom fun _ ↦ MonoidHom.id 𝐔ᶠ[k i × k j]

theorem bipartiteMonoidHom_apply (i j : ι) (h : i ≠ j) (U : 𝐔ᶠ[k i × k j]) :
    bipartiteMonoidHom' i j h U = bipartite' i j U h := by
  simp only [bipartiteMonoidHom', ne_eq, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp,
    MonoidHom.coe_coe, Function.comp_apply, bipartite', EmbeddingLike.apply_eq_iff_eq]
  ext
  simp

/-- The embedding of a unitary matrix `U : U[k × k]` into `𝐔[ι → k]` realized
by acting with `U` on the `i`th and the `j`th index, and trivially on all other
indices. -/
abbrev bipartite {k : Type*} [DecidableEq k] [Fintype k]
    (i j : ι) (U : 𝐔ᶠ[k × k]) (h : i ≠ j := by grind) := bipartite' (k := fun _ : ι ↦ k) i j U h

theorem bipartite_apply_basis (i j : ι) (A : 𝐔ᶠ[k i × k j]) (h : i ≠ j) (v : Π i, k i) :
    bipartite' i j A h δ[v] = ∑ q, A δ[(v i, v j)] q • δ[update (update v i q.1) j q.2] := by
  ext y
  simp only [bipartite'_coe_apply_ofLp, funext_iff, Subtype.forall, forall_and_index,
    basisVector_apply, ite_mul, one_mul, zero_mul, ← ite_and, and_comm, WithLp.ofLp_sum,
    WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp only [← funext_iff, ite_and, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Finset.sum_eq_single ⟨y i, y j⟩ (by aesop) (by aesop)]
  simp [funext_iff]
  grind

-- Another case of bad API.
theorem bipartite_apply_basis' (i j : ι) (U : 𝐔ᶠ[k i × k j]) (h : i ≠ j) (v : Π i, k i) :
    bipartite' i j U h δ[v] =
      (EuclideanSpace.piSplitAtPair i j) ((U δ[(v i, v j)]) ⨂ δ[fun a : {m // m ≠ i ∧ m ≠ j} => v a]) := by
  ext u
  simp only [bipartite_apply_basis, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply,
    Pi.smul_apply, basisVector_apply, funext_iff, smul_eq_mul, mul_ite, mul_one, mul_zero, ne_eq,
    EuclideanSpace.piSplitAtPair_apply, LinearEquiv.piCongrLeft'_apply, symm_symm,
    piSplitAtPair_apply, EuclideanSpace.outerProduct_apply, Subtype.forall, forall_and_index]
  simp_rw [← funext_iff, eq_update_iff, ne_eq, ite_and, Fintype.sum_prod_type, Finset.sum_ite_eq,
    Finset.mem_univ, funext_iff]
  rw [Finset.sum_eq_single (u i) (by grind) (by grind)]
  grind
