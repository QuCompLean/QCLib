module

public import QCLib.Circuit.Gate.BiPartite
public import QCLib.LinearAlgebra.PiOuterProduct.Equiv
public import QCLib.LinearAlgebra.UnitaryGroup.Kronecker

/-!

# Embedding unitary gates into larger systems

## Main Definitions

`single i U` : Embeds unitary `U[k]` to `𝐔[ι → k]` as `diag (U, U, ...)`.
Alternatively, it can be seen as `I ⊗ I ⊗ ... ⊗ U ⊗ ...` as shown in `single_eq_prod`.

`bipartite i j U` : Embeds unitary `U[k × k]` to `𝐔[ι → k]` as `diag (U, U, ...)`.
If `U = A[k] ⊗ B[k]`, embedding reduces to `I ⊗ I ⊗ ... ⊗ A ⊗ ... ⊗ B ⊗ ...`
as shown in `bipartite_kronecker`.

## TBD
Generalize this file to dependant case.

-/

@[expose] public section

open Matrix UnitaryGroup Function PiOuterProduct

variable {n} {k ι : Type*}

/-- `Equiv.finSplitAt` helper. -/
@[simp]
lemma flatten_ind (i) (a b : ι → k) :
    a i = b i ∧ ((fun j : { j // ¬j = i } ↦ a j) = fun j : { j // ¬j = i } ↦ b j) ↔ a = b := by
  simp [funext_iff]
  grind

variable [DecidableEq k] [DecidableEq ι] [Fintype k] [Fintype ι]

namespace Matrix.UnitaryGroup

section single

@[simps! coe]
def single (i : ι) (U : 𝐔[k]) : 𝐔[ι → k] :=
  reindexMonoidEquiv (Equiv.funSplitAt i k).symm (blockDiagonalMonoidHom (fun _ => U))

theorem single_eq_prod (i : ι) (U : 𝐔[k]) :
    single i U = ⨂ j, if j = i then U else 1 := by
  ext
  simp only [single_coe, submatrix_apply, Equiv.funSplitAt_apply, blockDiagonal_apply, funext_iff,
    Subtype.forall, piKroneckerUnitary_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single i] <;> aesop
  · obtain ⟨w, hw⟩ := not_forall.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ w) (by simp_all)]

theorem single_apply_apply (i : ι) (U : 𝐔[k]) (a b : ι → k) :
    single i U a b = if ∀ k ≠ i, a k = b k then U (a i) (b i) else 0 := by
  simp [blockDiagonal_apply, funext_iff]

@[simp]
theorem single_diagonal (d : k → unitary ℂ) (i : ι) :
    single i (diagonalMonoidHom d) = diagonalMonoidHom fun k ↦ d (k i) := by
  ext
  simp [diagonal_apply]

-- TBD : Old proof, clean up
theorem single_apply_basis (v : ι → k) (j : ι) (U : 𝐔[k]) :
    single j U • δ[v] = ∑ q, U q (v j) • δ[update v j q] := by
  ext k
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, single_apply_apply, one_smul,
    Finset.sum_apply, Pi.single_apply, smul_eq_mul, funext_iff]
  split_ifs
  · rw [Finset.sum_eq_single (k j)] <;> grind
  · rw [Finset.sum_eq_zero]; grind

@[simp]
theorem single_single_commute {i j : ι} (h : i ≠ j) (U V : 𝐔[k]) :
    Commute (single i U) (single j V) := by
  simp only [single_eq_prod, commute_iff_eq, mul_piKroneckerUnitary_mul]
  congr
  grind

theorem single_mul (i : ι) (U V : 𝐔[k]) :
    single i (U * V) = single i U * single i V := by
  ext
  simp

@[simp]
theorem pairwise_commute_single (f : ι → 𝐔[k]) (s : Set ι) :
    s.Pairwise (Function.onFun Commute (fun i ↦ single i (f i))) :=
  (fun x _ y _ hneq ↦ single_single_commute hneq (f x) (f y))

@[simp]
theorem noncommProd_single (f : ι → 𝐔[k]) (s : Finset ι) :
    s.noncommProd (fun i ↦ single i (f i)) (by simp) = ⨂ i, if (i ∈ s) then f i else 1 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha IH =>
    have (i : ι) : (if i = a ∨ i ∈ s then f i else 1) =
        (if i = a then f a else 1) * (if i ∈ s then f i else 1) := by grind
    simp_rw [Finset.noncommProd_cons, IH, Finset.cons_eq_insert, Finset.mem_insert, this,
    ← mul_piKroneckerUnitary_mul, single_eq_prod]

end single


section bipartite

@[simps!]
def bipartite (i j : ι) (U : 𝐔[k × k]) (h : i ≠ j := by grind) :=
  (reindexMonoidEquiv (funSplitTwo i j (Ne.symm h) (l := k)).symm)
    (blockDiagonalMonoidHom (fun _ => U))

theorem bipartite_apply_apply (A : 𝐔[k × k])
    (i j : ι) (h : i ≠ j) (a b : ι → k) :
    bipartite i j A h a b =
      if ∀ k, k ≠ i → k ≠ j → a k = b k then A (a i, a j) (b i, b j) else 0 := by
  simp [blockDiagonal_apply, funext_iff]

set_option backward.isDefEq.respectTransparency false in
theorem bipartite_kronecker (A B : 𝐔[k]) (i j : ι) (h : i ≠ j) :
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
theorem bipartite_apply_basis (A : 𝐔[k × k]) (i j : ι) (h : i ≠ j) (v : ι → k) :
    bipartite i j A • δ[v] = ∑ q, A q (v i, v j) • δ[update (update v i q.1) j q.2] := by
  ext w
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, bipartite_apply_apply, one_smul, Finset.sum_apply,
    Pi.single_apply, smul_eq_mul, funext_iff, update_apply]
  split_ifs
  · rw [Finset.sum_eq_single (w i, w j)] <;> grind
  · rw [Finset.sum_eq_zero]; grind

@[simp]
theorem bipartite_diagonal (d : ι × ι → unitary ℂ) (i j : Fin n) (h : i ≠ j) :
    bipartite i j (diagonalMonoidHom d) = diagonalMonoidHom fun k ↦ d (k i, k j) := by
  ext
  simp [diagonal_apply, funext_iff]
  grind

@[simp]
theorem controllize_of_zero {n} (U : 𝐔[Qubit]) (i j : Fin n) (h : i ≠ j)
    (v : Register n) (hv : v j = 0) : bipartite i j C[U] • δ[v] = δ[v] := by
  ext w
  by_cases hw : v = w
  all_goals
    simp_all [basisVector_def, Submonoid.smul_def, funext_iff, blockDiagonal_apply,
      Pi.single_apply, Matrix.one_apply]
    try grind

@[simp]
theorem controllize_of_one {n : ℕ} (U : 𝐔[Qubit]) (i j : Fin n.succ) (h : i ≠ j)
    (v : Register n.succ) (hv : v j = 1) :
    bipartite i j C[U] • δ[v] = ∑ q, U q (v i) • δ[update v i q] := by
  ext w
  by_cases hw : v = w
  all_goals
    simp_all [basisVector_def, Submonoid.smul_def, funext_iff, blockDiagonal_apply,
      Pi.single_apply]
    grind

end bipartite

end Matrix.UnitaryGroup
