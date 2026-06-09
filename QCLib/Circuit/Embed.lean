module

public import QCLib.Circuit.Gate.BiPartite
public import QCLib.LinearAlgebra.PiOuterProduct.Equiv
public import QCLib.LinearAlgebra.UnitaryGroup.Kronecker

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

open Function PiOuterProduct

variable {n} {ι : Type*} {k : ι → Type*}
  [∀ i, DecidableEq (k i)] [DecidableEq ι] [∀ i, Fintype (k i)] [Fintype ι]

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

theorem single_apply_apply (i : ι) (U : 𝐔[k i]) (a b : (i : ι) → k i) :
    single' i U a b = if ∀ k ≠ i, a k = b k then U (a i) (b i) else 0 := by
  simp [blockDiagonal_apply, funext_iff]

theorem single_diagonal (i : ι) (d : k i → unitary ℂ) :
    single' i (diagonalMonoidHom d) = diagonalMonoidHom (fun x ↦ d (x i)) := by
  ext
  simp [diagonal_apply, funext_iff]
  grind

-- TBD: Old proof, clean up
theorem single_apply_basis (v : (i : ι) → (k i)) (j : ι) (U : 𝐔[k j]) :
    single' j U • δ[v] = ∑ q, U q (v j) • δ[update v j q] := by
  ext k
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, single_apply_apply, one_smul,
    Finset.sum_apply, Pi.single_apply, smul_eq_mul, funext_iff]
  split_ifs
  · rw [Finset.sum_eq_single (k j)] <;> grind
  · rw [Finset.sum_eq_zero]; grind

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
theorem pairwise_commute_single (f : (i : ι) → 𝐔[k i]) (s : Set ι) :
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

/-! The embedding of a unitary matrix `U : U[k i × k j]` into `𝐔[Π i, k i]`
realized by acting with `U` on the `i`th and the `j`th index, and trivially on
all other indices. -/
@[simps!]
def bipartite' (i j : ι) (U : 𝐔[k i × k j]) (h : i ≠ j := by grind) : 𝐔[Π i, k i] :=
  (reindexMonoidEquiv (piSplitTwo i j (Ne.symm h) (β := k)).symm)
    (blockDiagonalMonoidHom (fun _ ↦ U))

/-! The embedding of a unitary matrix `U : U[k × k]` into `𝐔[ι → k]` realized
by acting with `U` on the `i`th and the `j`th index, and trivially on all other
indices. -/
abbrev bipartite {k : Type*} [DecidableEq k] [Fintype k]
    (i j : ι) (U : 𝐔[k × k]) (h : i ≠ j := by grind) :=
  bipartite' (k := fun _ : ι => k) i j U h

theorem bipartite_apply_apply (i j : ι) (A : 𝐔[k i × k j]) (h : i ≠ j) (a b : (i : ι) → (k i)) :
    bipartite' i j A h a b =
      if ∀ k, k ≠ i → k ≠ j → a k = b k then A (a i, a j) (b i, b j) else 0 := by
  simp [blockDiagonal_apply, funext_iff]

-- TBD : Generalize it to dependent case
set_option backward.isDefEq.respectTransparency false in
theorem bipartite_kronecker {k : Type*} [DecidableEq k] [Fintype k]
    (A B : 𝐔[k]) (i j : ι) (h : i ≠ j) :
    bipartite i j (A ⊗ᵤ B) = ⨂ k, if k = i then A else if k = j then B else 1 := by
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

@[simp]
theorem bipartite_apply_basis (i j : ι) (A : 𝐔[k i × k j]) (h : i ≠ j) (v : (i : ι) → (k i)) :
    bipartite' i j A • δ[v] = ∑ q, A q (v i, v j) • δ[update (update v i q.1) j q.2] := by
  ext w
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, bipartite_apply_apply, one_smul, Finset.sum_apply,
    Pi.single_apply, smul_eq_mul, funext_iff]
  split_ifs
  · rw [Finset.sum_eq_single (w i, w j)] <;> grind
  · rw [Finset.sum_eq_zero]; grind

@[simp]
theorem bipartite_diagonal (d : Π i j, k i → k j → unitary ℂ) (i j : ι) (h : i ≠ j) :
  bipartite' i j (diagonalMonoidHom (fun p : k i × k j => d i j p.1 p.2)) =
    diagonalMonoidHom (fun x : (j : ι) → k j => d i j (x i) (x j)) := by
  ext a b
  simp [diagonal_apply, funext_iff]

@[simp]
theorem controllize_of_zero {n} (U : 𝐔[Qubit]) (i j : Fin n) (h : i ≠ j)
    (v : Register n) (hv : v i = 0) : bipartite i j C[U] • δ[v] = δ[v] := by
  ext w
  by_cases hw : v = w
  all_goals
    simp_all [basisVector_def, Submonoid.smul_def, funext_iff, blockDiagonal_apply,
      Pi.single_apply, Matrix.one_apply]
    try grind

@[simp]
theorem controllize_of_one {n : ℕ} (U : 𝐔[Qubit]) (i j : Fin n.succ) (h : i ≠ j)
    (v : Register n.succ) (hv : v i = 1) :
    bipartite i j C[U] • δ[v] = ∑ q, U q (v j) • δ[update v j q] := by
  ext w
  by_cases hw : v = w
  all_goals
    simp_all [basisVector_def, Submonoid.smul_def, funext_iff, blockDiagonal_apply,
      Pi.single_apply]
    grind

end bipartite

end Matrix.UnitaryGroup
