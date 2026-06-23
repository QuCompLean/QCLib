/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import QCLib.Circuit.Gate.Bipartite
public import QCLib.Logic.Equiv
public import QCLib.LinearAlgebra.OuterProduct
public import QCLib.LinearAlgebra.UnitaryGroup.Kronecker
public import QCLib.Logic.Equiv

/-!

# Embedding unitary gates into larger systems

## Main Definitions

* `single i U` : The embedding of a unitary matrix `U : 𝐔[k]` into `𝐔[ι → k]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices.

* `bipartite i j U` : The embedding of a unitary matrix `U : U[k × k]` into `𝐔[ι → k]`
realized by acting with `U` on the `i`th and the `j`th index, and trivially on all other indices.

For the dependent case, use `single'` and `bipartite'`.

## Main results

TBD

-/

@[expose] public section

open Function PiOuterProduct OuterProduct Equiv

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {k : ι → Type*} [∀ i, DecidableEq (k i)] [∀ i, Fintype (k i)]

namespace Matrix.UnitaryGroup

section single

/-- The embedding of a unitary matrix `U : 𝐔[k i]` into `𝐔[Π i, k i]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices. -/
@[simps! coe]
def single' (i : ι) (U : 𝐔[k i]) : 𝐔[Π i, k i] :=
  reindexMonoidEquiv (Equiv.piSplitAt i k).symm (blockDiagonalMonoidHom (fun _ ↦ U))

/-- The embedding of a unitary matrix `U : 𝐔[k]` into `𝐔[ι → k]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices. -/
abbrev single {k : Type*} [DecidableEq k] [Fintype k] (i : ι) (U : 𝐔[k]) :=
  single' (k := fun _ ↦ k) i U

theorem single_eq_prod (i : ι) (U : 𝐔[k i]) :
    single' i U = ⨂ j, if h : j = i then h ▸ U else (1 : 𝐔[k j]) := by
  ext
  simp only [single'_coe, submatrix_apply, blockDiagonal_apply, funext_iff,
    Subtype.forall, piKroneckerUnitary_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single i] <;> aesop
  · obtain ⟨w, hw⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp_all)]

example {k : Type*} [DecidableEq k] [Fintype k] (i : ι) (U : 𝐔[k]) :
    single i U = ⨂ j, if j = i then U else 1 := by
  simp [single_eq_prod]

@[simp]
theorem single_one (i : ι) : single' i (1 : 𝐔[k i]) = 1 := by
  ext
  simp [blockDiagonal_apply, funext_iff, Matrix.one_apply]
  grind

theorem single_apply_apply (i : ι) (U : 𝐔[k i]) (a b : Π i, k i) :
    single' i U a b = if ∀ k ≠ i, a k = b k then U (a i) (b i) else 0 := by
  simp [blockDiagonal_apply, funext_iff]

theorem single'_reindexMonoidEquiv {k' : ι → Type*}
    [∀ i, DecidableEq (k' i)] [∀ i, Fintype (k' i)]
    (e : ∀ i, k i ≃ k' i) (i : ι) (U : 𝐔[k i]) :
    single' i (reindexMonoidEquiv (e i) U) =
    reindexMonoidEquiv (Equiv.piCongrRight e) (single' i U) := by
  ext
  simp [blockDiagonal_apply, funext_iff]

theorem single_reindexMonoidEquiv {k k' : Type*} [DecidableEq k] [DecidableEq k']
    [Fintype k] [Fintype k'] (e : k ≃ k') (i : ι) (U : 𝐔[k]) :
    single i (reindexMonoidEquiv e U) =
    reindexMonoidEquiv (piCongrRight (fun _ : ι ↦ e)) (single i U) := by
  simp [← single'_reindexMonoidEquiv]

theorem single_diagonal (i : ι) (d : k i → unitary ℂ) :
    single' i (diagonalMonoidHom d) = diagonalMonoidHom (fun x ↦ d (x i)) := by
  ext
  simp [diagonal_apply, funext_iff]
  grind

-- TBD: Old proof, clean up
theorem single_apply_basis (v : Π i, k i) (j : ι) (U : 𝐔[k j]) :
    single' j U • δ[v] = ∑ q, U q (v j) • δ[update v j q] := by
  ext k
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, single_apply_apply, one_smul,
    Finset.sum_apply, Pi.single_apply, smul_eq_mul, funext_iff]
  split_ifs
  · rw [Finset.sum_eq_single (k j)] <;> grind
  · rw [Finset.sum_eq_zero]; grind

theorem single_apply_basis' (v : Π i, k i) (i : ι) (U : 𝐔[k i]) :
    single' i U • δ[v] = (U • δ[v i]) ⊗ δ[fun a : {j // j ≠ i} => v a] ∘ piSplitAt i _ := by
  ext
  simp [basisVector_def, Submonoid.smul_def, blockDiagonal_apply, Pi.single_apply]

@[simp]
theorem single_single_commute {i j : ι} (h : i ≠ j) (U : 𝐔[k i]) (V : 𝐔[k j]) :
    Commute (single' i U) (single' j V) := by
  simp only [single_eq_prod, commute_iff_eq, mul_piKroneckerUnitary_mul]
  congr
  grind

theorem single_mul (i : ι) (U V : 𝐔[k i]) :
    single' i (U * V) = single' i U * single' i V := by
  ext
  simp

@[simp]
theorem pairwise_commute_single (f : Π i, 𝐔[k i]) (s : Set ι) :
    s.Pairwise (Function.onFun Commute (fun i ↦ single' i (f i))) :=
  (fun x _ y _ hneq ↦ single_single_commute hneq (f x) (f y))

-- TBD : Generalize it to dependent case
theorem noncommProd_single {k : Type*} [DecidableEq k] [Fintype k] (f : ι → 𝐔[k]) (s : Finset ι) :
    s.noncommProd (fun i ↦ single i (f i)) (by simp) = ⨂ i, if (i ∈ s) then f i else 1 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha IH =>
    have (i : ι) : (if i = a ∨ i ∈ s then f i else 1) =
        (if i = a then f a else 1) * (if i ∈ s then f i else 1) := by grind
    simp_rw [Finset.noncommProd_cons, IH, Finset.cons_eq_insert, Finset.mem_insert, this,
      ← mul_piKroneckerUnitary_mul, single_eq_prod]
    simp

theorem noncommProd_single_univ {k : Type*} [DecidableEq k] [Fintype k] (f : ι → 𝐔[k]) :
    Finset.noncommProd Finset.univ (fun i ↦ single i (f i)) (by simp) = ⨂ i, f i := by
  simp [noncommProd_single]

end single


section bipartite

-- TBD: Revisit argument order
/-! The embedding of a unitary matrix `U : U[k i × k j]` into `𝐔[Π i, k i]`
realized by acting with `U` on the `i`th and the `j`th index, and trivially on
all other indices. -/
@[simps!]
def bipartite' (i j : ι) (U : 𝐔[k i × k j]) (h : i ≠ j := by grind) : 𝐔[Π i, k i] :=
  reindexMonoidEquiv (Equiv.piSplitAtPair i j h.symm).symm <| blockDiagonalMonoidHom (fun _ ↦ U)

/-! `Matrix.UnitaryGroup.bipartite'` bundled as a monoid homomorphism. -/
def bipartiteMonoidHom' (i j : ι) (h : i ≠ j := by grind) : 𝐔[k i × k j] →* 𝐔[Π i, k i] :=
  (reindexMonoidEquiv (Equiv.piSplitAtPair i j h.symm).symm).toMonoidHom.comp
    <| blockDiagonalMonoidHom.comp
      <| Pi.monoidHom fun _ ↦ MonoidHom.id 𝐔[k i × k j]

theorem bipartiteMonoidHom_apply (i j : ι) (h : i ≠ j) (U : 𝐔[k i × k j]) :
    bipartiteMonoidHom' i j h U = bipartite' i j U h := by
  simp only [bipartiteMonoidHom', ne_eq, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp,
    MonoidHom.coe_coe, Function.comp_apply, bipartite', EmbeddingLike.apply_eq_iff_eq]
  ext
  simp

/-! The embedding of a unitary matrix `U : U[k × k]` into `𝐔[ι → k]` realized
by acting with `U` on the `i`th and the `j`th index, and trivially on all other
indices. -/
abbrev bipartite {k : Type*} [DecidableEq k] [Fintype k]
    (i j : ι) (U : 𝐔[k × k]) (h : i ≠ j := by grind) := bipartite' (k := fun _ : ι ↦ k) i j U h

theorem bipartite_apply_apply (i j : ι) (A : 𝐔[k i × k j]) (h : i ≠ j) (a b : Π i, k i) :
    bipartite' i j A h a b =
      if ∀ k, k ≠ i → k ≠ j → a k = b k then A (a i, a j) (b i, b j) else 0 := by
  simp [blockDiagonal_apply, funext_iff]

-- TBD : Generalize it to dependent case
set_option backward.isDefEq.respectTransparency false in
theorem bipartite_kronecker {k : Type*} [DecidableEq k] [Fintype k]
    (A B : 𝐔[k]) (i j : ι) (h : i ≠ j) :
    bipartite i j (A ⊗ᵤ B) h = ⨂ k, if k = i then A else if k = j then B else 1 := by
  ext k l
  simp only [bipartite_apply_apply, ne_eq, coe_piKroneckerUnitary, piKronecker_apply]
  split_ifs with hv
  · have (i : ι) : Finset.card {x | x = i} = 1 := Finset.card_eq_one.mpr (by use i; grind)
    push_cast
    simp_rw [apply_ite Subtype.val, ite_apply _]
    simp_all [Finset.prod_ite, Ne.symm h]
  · obtain ⟨w, hw⟩ := not_forall.mp hv
    refine (Finset.prod_eq_zero (Finset.mem_univ w) ?_).symm
    simp_all

theorem bipartite_apply_basis (i j : ι) (A : 𝐔[k i × k j]) (h : i ≠ j) (v : Π i, k i) :
    bipartite' i j A h • δ[v] = ∑ q, A q (v i, v j) • δ[update (update v i q.1) j q.2] := by
  ext w
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, bipartite_apply_apply, one_smul, Finset.sum_apply,
    Pi.single_apply, smul_eq_mul, funext_iff]
  split_ifs
  · rw [Finset.sum_eq_single (w i, w j)] <;> grind
  · rw [Finset.sum_eq_zero]; grind

theorem bipartite_apply_basis' (i j : ι) (U : 𝐔[k i × k j]) (h : i ≠ j) (v : Π i, k i) :
    bipartite' i j U h • δ[v] =
      ((U • δ[(v i, v j)]) ⊗ δ[fun a : {m // m ≠ i ∧ m ≠ j} => v a]) ∘ (piSplitAtPair i j) := by
  ext
  simp [basisVector_def, Submonoid.smul_def, blockDiagonal_apply, funext_iff, Pi.single_apply]

@[simp]
theorem bipartite_diagonal (i j : ι) (d : k i × k j → unitary ℂ) (h : i ≠ j) :
    bipartite' i j (diagonalMonoidHom d) h = diagonalMonoidHom (fun x ↦ d (x i, x j)) := by
  ext a b
  simp [diagonal_apply, funext_iff]

@[simp]
theorem controllize_of_zero {n} (U : 𝐔[Qubit]) (i j : Fin n) (h : i ≠ j)
    (v : Register n) (hv : v i = 0) : bipartite i j C[U] h • δ[v] = δ[v] := by
  ext w
  by_cases hw : v = w
  all_goals
    simp_all [basisVector_def, Submonoid.smul_def, funext_iff, blockDiagonal_apply,
      Pi.single_apply, Matrix.one_apply]
    try grind

@[simp]
theorem controllize_of_one {n : ℕ} (U : 𝐔[Qubit]) (i j : Fin n.succ) (h : i ≠ j)
    (v : Register n.succ) (hv : v i = 1) :
    bipartite i j C[U] h • δ[v] = ∑ q, U q (v j) • δ[update v j q] := by
  ext w
  by_cases hw : v = w
  all_goals
    simp_all [basisVector_def, Submonoid.smul_def, funext_iff, blockDiagonal_apply,
      Pi.single_apply]
    grind

end bipartite


section subtype

@[simps!]
def subtype (p : ι → Prop) [DecidablePred p]
    (U : 𝐔[Π i : {j // p j}, k i.1]) : 𝐔[Π i, k i] :=
  reindexMonoidEquiv (Equiv.piEquivPiSubtypeProd p k).symm <| blockDiagonalMonoidHom (fun _ ↦ U)

theorem subtype_apply_basis (p : ι → Prop) [DecidablePred p]
    (U : 𝐔[Π i : {j // p j}, k i.1]) (v : Π i, k i)  :
    subtype p U • δ[v] =
      ((U • δ[fun i : {j // p j} => v i.1])
        ⊗ (δ[fun i : {j // ¬ p j} => v i.1])) ∘ (Equiv.piEquivPiSubtypeProd p k) := by
  ext
  simp [basisVector_def, Submonoid.smul_def, blockDiagonal_apply, funext_iff, Pi.single_apply]

end subtype

section Fin

variable {n : ℕ}
variable {k : Type*} [DecidableEq k] [Fintype k]

@[simps!]
def embedRight (U : 𝐔[Fin n → k]) : 𝐔[Fin (n + 1) → k] :=
  reindexMonoidEquiv (Fin.consFunEquiv n k) <| blockDiagonalMonoidHom (fun _ ↦ U)

/-! The embedding of a unitary matrix `U : U[Fin n → k]` into `𝐔[Fin (n+1) → k]`
realized by acting with `U` on the last `n` subsystems and trivially on the first one. -/
theorem embedRight_apply_basis (U : 𝐔[Fin n → k]) (v : Fin (n + 1) → k) :
    embedRight U • δ[v] =
      ((U • δ[fun i : Fin n => v i.succ]) ⊗ δ[v 0]) ∘ (Fin.consFunEquiv n k).symm := by
  ext
  simp [basisVector_def, Submonoid.smul_def, blockDiagonal_apply, Pi.single_apply]
  rfl

/-! The embedding of a unitary matrix `U : 𝐔[Fin n → k]` into `𝐔[Fin (n+1) → k]`
realized by acting with `U` on the first `n` subsystems and trivially on the final one. -/
@[simps!]
def embedLeft (U : 𝐔[Fin n → k]) : 𝐔[Fin (n + 1) → k] :=
  reindexMonoidEquiv (Fin.succFunEquiv k n).symm <| blockDiagonalMonoidHom (fun _ ↦ U)

theorem embedLeft_apply_basis (U : 𝐔[Fin n → k]) (v : Fin (n + 1) → k) :
    embedLeft U • δ[v] =
      ((U • δ[fun i : Fin n => v i.castSucc]) ⊗ δ[v (Fin.last n)])
      ∘ Fin.succFunEquiv k n := by
  ext
  simp [basisVector_def, Submonoid.smul_def, blockDiagonal_apply, Pi.single_apply]
  rfl -- There seems to be no connection between Fin.last n and Fin.natAdd n 0


variable {m d : ℕ} (h : n ≤ m)

/-- The embedding of a unitary matrix `U : 𝐔[Fin n → k]` into `𝐔[Fin m → k]` with
    `n ≤ m` realized by acting with `U` on the first `n` subystems and trivially on the rest.
    As it satisfies both identity and transitivity conditions, it forms a `Directed System`.
-/
@[simps! coe]
def embedFin (U : 𝐔[Fin n → k]) : 𝐔[Fin m → k] :=
  subtype (fun i : Fin m ↦ i.val < n) (reindexMonoidEquiv (finFunSubtypeEquiv k h) U)

theorem embedFin_mul (U V : 𝐔[Fin n → k]) :
    embedFin h (U * V) = embedFin h U * embedFin h V := by
  ext
  simp [embedFin, ← blockDiagonal_mul]

@[simp]
theorem embedFin_map_self (U : 𝐔[Fin n → k]) : embedFin (le_refl n) U = U := by
  ext
  simp [blockDiagonal_apply, funext_iff, finFunSubtypeEquiv, piCongrLeft']

@[simp]
theorem embedFin_trans {p} (U : 𝐔[Fin n → k]) (hn : n ≤ p) (hp : p ≤ m) :
    embedFin hp (embedFin hn U) = embedFin (le_trans hn hp) U := by
  ext a b
  simp [embedFin, blockDiagonal_apply, funext_iff, finFunSubtypeEquiv, piCongrLeft']
  split_ifs with h1 h2 h3 <;> try grind
  obtain ⟨q, hq⟩ := not_forall.mp h3
  by_cases hkq : p ≤ q
  · have := h1 q
    simp_all
  · simp only [not_le] at hkq
    have := h2 ⟨q, hkq⟩
    exfalso
    exact hq (by simp_all)

-- TBD : Add DirectedSystem instance?

theorem embedFin_single_castAdd (p) (i : Fin n) (U : 𝐔[k]) :
    embedFin le_self_add (single i U) = single (i.castAdd p) U := by
  ext i j
  simp [blockDiagonal_apply, funext_iff, ← ite_and]
  split_ifs with h1 h2 <;> try grind
  exfalso
  have ⟨x, hx⟩ := not_forall.mp h2
  by_cases hnx : n ≤ x
  · have := h1.1 x hnx
    simp_all
  · have := h1.2 ⟨x, by lia⟩ (by grind)
    simp_all

theorem embedFin_diagonalMonoidHom_castAdd (k : ℕ) (f : (Fin n → Fin d) → (unitary ℂ)) :
    embedFin le_self_add (diagonalMonoidHom f)
      = diagonalMonoidHom
          (fun y : Fin (n + k) → Fin d ↦ f (fun i ↦ y (i.castAdd k))) := by
  ext i j
  simp [diagonal_apply, funext_iff]
  split_ifs with h1 h2 <;> try grind
  rfl

/-- `embedFin` as `MonoidHom`. Could be useful in some contexts, when
  homorophisms are necessary, such as `List.prod_map_hom` -/
@[simps! -isSimp apply]
def embedFinHom : 𝐔[Fin n → Fin d] →* 𝐔[Fin m → Fin d] :=
  MonoidHom.mk' (embedFin h) (embedFin_mul _)

end UnitaryGroup.Fin
end Matrix
