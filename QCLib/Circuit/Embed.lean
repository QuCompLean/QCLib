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

variable {ι : Type*}
variable {k : ι → Type*}

/-- `funext_iff` specialized to functions out of the "complement of `{i}`" subtype,
so `simp` won't also unfold unrelated `Π i, k i` equalities like `x = v`. -/
@[simp]
theorem funext_iff_ne {i : ι} :
    ∀ {f g : ∀ a : {ℓ // ℓ ≠ i}, k a.1}, f = g ↔ ∀ a, f a = g a := funext_iff

/-- Same, for the pair of `{i, j}`. -/
@[simp]
theorem funext_iff_ne_ne {i j : ι} :
    ∀ {f g : ∀ a : {ℓ // ℓ ≠ i ∧ ℓ ≠ j}, k a.1}, f = g ↔ ∀ a, f a = g a := funext_iff

@[simp]
theorem eq_iff_eq_of_eq_at (i : ι) (x y : (j : ι) → k j) :
   (∀ (a : ι), ¬a = i → x a = y a) ∧ x i = y i ↔ x = y := by grind

variable [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (k i)] [∀ i, Fintype (k i)]

@[simp]
theorem sum_update_eq {M} [AddCommMonoid M] (i : ι)
    (x v : (j : ι) → k j) (f : k i → M) :
    (∑ t : k i, if x = update v i t then f t else 0) =
      if ∀ a, a ≠ i → x a = v a then f (x i) else 0 := by
  simp [eq_update_iff, ite_and]

@[simp]
theorem sum_update_update_eq {M} [AddCommMonoid M] {i j : ι}
    (hij : i ≠ j)
    (y v : (a : ι) → k a)
    (f : k i × k j → M) :
    (∑ x, if y = update (update v i x.1) j x.2 then f x else 0) =
      if ∀ a, a ≠ i → a ≠ j → y a = v a then f (y i, y j) else 0 := by
  simp only [Fintype.sum_prod_type, sum_update_eq, ne_eq]
  rw [Finset.sum_eq_single (y i)] <;> grind

@[simp]
theorem ContinuousLinearMap.dite_apply
    {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
    {σ₁₂ : R₁ →+* R₂}
    {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
    {p : Prop} [Decidable p]
    (f : p → M₁ →SL[σ₁₂] M₂)
    (g : ¬p → M₁ →SL[σ₁₂] M₂)
    (x : M₁) :
    (dite p f g) x = dite p (fun h => f h x) (fun h => g h x) := by
  grind

@[simp]
theorem ContinuousLinearMap.ite_apply
    {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂]
    {σ₁₂ : R₁ →+* R₂}
    {M₁ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [Module R₁ M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₂ M₂]
    {p : Prop} [Decidable p]
    (f g : M₁ →SL[σ₁₂] M₂)
    (x : M₁) :
    (if p then f else g) x = if p then f x else g x := by
  grind

section single

/-- The embedding of a unitary matrix `U : 𝐔ᶠ[k i]` into `𝐔ᶠ[Π i, k i]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices. -/
@[simps! -isSimp coe]
def single' (i : ι) (U : 𝐔ᶠ[k i]) : 𝐔ᶠ[Π i, k i] :=
  reindexMonoidEquiv (piSplitAt i k).symm (blockDiagonalStarMonoidHom (fun _ ↦ U))

/-- The embedding of a unitary matrix `U : 𝐔ᶠ[k]` into `𝐔ᶠ[ι → k]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices. -/
abbrev single {k : Type*} [DecidableEq k] [Fintype k] (i : ι) (U : 𝐔ᶠ[k]) :=
  single' (k := fun _ ↦ k) i U

attribute [simp] mulVec_eq_sum blockDiagonal_apply ite_apply

@[simp]
theorem single_apply_basis (v : Π i, k i) (i : ι) (U : 𝐔ᶠ[k i]) :
    single' i U δ[v] =
      ∑ w, (U δ[v i]) w • δ[update v i w] := by
  ext
  simp [single'_coe, eq_comm]

theorem single_apply_basis' (v : Π i, k i) (i : ι) (U : 𝐔ᶠ[k i]) :
    single' i U δ[v] = EuclideanSpace.piSplitAt i
      ((U δ[v i]) ⨂ δ[fun a : {j // j ≠ i} => v a]) := by
  ext
  simp [eq_update_iff, ite_and]

@[simp]
theorem single_one (i : ι) : single' i (1 : 𝐔ᶠ[k i]) = 1 := by
  ext
  simp

theorem single'_reindexMonoidEquiv {k' : ι → Type*} [∀ i, DecidableEq (k' i)] [∀ i, Fintype (k' i)]
    (e : ∀ i, k i ≃ k' i) (i : ι) (U : 𝐔ᶠ[k i]) :
    single' i (reindexMonoidEquiv (e i) U) =
      reindexMonoidEquiv (piCongrRight e) (single' i U) := by
  ext
  simp [Unitary.EuclideanCLM.reindexMonoidEquiv]

theorem single_reindexMonoidEquiv {k k' : Type*} [DecidableEq k] [DecidableEq k']
    [Fintype k] [Fintype k'] (e : k ≃ k') (i : ι) (U : 𝐔ᶠ[k]) :
    single i (reindexMonoidEquiv e U) =
    Unitary.EuclideanCLM.reindexMonoidEquiv (piCongrRight (fun _ : ι ↦ e)) (single i U) := by
  simp [← single'_reindexMonoidEquiv]

theorem single_diagonal (i : ι) (d : k i → unitary ℂ) :
    single' i (diagonalMonoidHom d) = diagonalMonoidHom (fun x ↦ d (x i)) := by
  ext
  simp [diagonalMonoidHom_coe, diagonal_apply, eq_comm]

theorem single_eq_prod (i : ι) (U : 𝐔ᶠ[k i]) :
    single' i U = ⨂ j, if h : j = i then h ▸ U else (1 : 𝐔ᶠ[k j]) := by
  ext
  simp only [single_apply_basis, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
    basisVector_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sum_update_eq, ne_eq, piTprod_coe,
    apply_dite, OneMemClass.coe_one, EuclideanCLM.piTprod_apply, map_one, mulVec_eq_sum,
    op_smul_eq_smul, ite_smul, one_smul, zero_smul, ite_apply, transpose_apply, piKronecker_apply,
    Pi.zero_apply, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  split_ifs with h
  · rw [Finset.prod_eq_single i] <;> simp_all [one_apply]
  · obtain ⟨w, hw⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp_all )]

example {k : Type*} [DecidableEq k] [Fintype k] (i : ι) (U : 𝐔ᶠ[k]) :
    single i U = ⨂ j, if j = i then U else 1 := by
  simp [single_eq_prod]

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
  simp [single'_coe, ← blockDiagonal_mul, ← map_mul]

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
@[simps! -isSimp coe]
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

@[simp]
theorem bipartite_apply_basis (i j : ι) (A : 𝐔ᶠ[k i × k j]) (h : i ≠ j) (v : Π i, k i) :
    bipartite' i j A h δ[v] = ∑ q, A δ[(v i, v j)] q • δ[update (update v i q.1) j q.2] := by
  ext
  simp [bipartite'_coe, sum_update_update_eq h]
  simp [eq_comm_eq]

theorem bipartite_apply_basis' (i j : ι) (U : 𝐔ᶠ[k i × k j]) (h : i ≠ j) (v : Π i, k i) :
    bipartite' i j U h δ[v] =
      (EuclideanSpace.piSplitAtPair i j)
      ((U δ[(v i, v j)]) ⨂ δ[fun a : {m // m ≠ i ∧ m ≠ j} => v a]) := by
  ext
  simp [sum_update_update_eq h]

@[simp]
theorem bipartite_diagonal (i j : ι) (d : k i × k j → unitary ℂ) (h : i ≠ j) :
    bipartite' i j (diagonalMonoidHom d) h = diagonalMonoidHom (fun x ↦ d (x i, x j)) := by
  ext
  simp_all

-- TBD : Generalize it to dependent case
theorem bipartite_kronecker {k : Type*} [DecidableEq k] [Fintype k]
    (A B : 𝐔ᶠ[k]) (i j : ι) (h : i ≠ j) :
    bipartite i j (A ⨂ B) h = ⨂ k, if k = i then A else if k = j then B else 1 := by
  ext n m
  simp only [bipartite_apply_basis', ne_eq, EuclideanSpace.piSplitAtPair_apply,
    LinearEquiv.piCongrLeft'_apply, symm_symm, piSplitAtPair_apply,
    EuclideanSpace.outerProduct_apply, tensorProduct_apply, unitaryGroupEquiv_symm_apply,
    UnitaryGroup.kronecker_apply, Subtype.map_coe, StarMulEquiv.toStarMonoidHom_coe,
    StarMulEquiv.ofClass_symm_apply, StarAlgEquiv.invFun_eq_symm, mulVec_eq_sum, basisVector_apply,
    op_smul_eq_smul, ite_smul, one_smul, zero_smul, Finset.sum_apply, ite_apply, transpose_apply,
    kroneckerMap_apply, toEuclideanCLM_symm_apply, Pi.zero_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, mul_ite, mul_one, mul_zero, piTprod_coe,
    EuclideanCLM.piTprod_apply, piKronecker_apply]
  simp only [funext_iff, Subtype.forall, forall_and_index, apply_ite (Subtype.val),
    OneMemClass.coe_one, ContinuousLinearMap.ite_apply, ContinuousLinearMap.one_apply,
    apply_ite (WithLp.ofLp), ite_apply, basisVector_apply]
  split_ifs with hv
  · have (i : ι) : Finset.card {x | x = i} = 1 := Finset.card_eq_one.mpr (by use i; grind)
    simp_all [Finset.prod_ite, Ne.symm h]
  · simp_all [Finset.prod_ite]
