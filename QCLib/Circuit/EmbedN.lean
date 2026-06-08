module

public import QCLib.Circuit.Gate.BiPartite
public import QCLib.LinearAlgebra.PiOuterProduct.Equiv
public import QCLib.LinearAlgebra.UnitaryGroup.Kronecker


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

theorem singleQubit_mul (i : Fin n) (U V : 𝐔[Qubit]) :
    single i (U * V) = single i U * single i V := by
  ext
  simp

@[simp]
theorem pairwise_commute_singleQubit (f : ι → 𝐔[k]) (s : Set ι) :
    s.Pairwise (Function.onFun Commute (fun i ↦ single i (f i))) :=
  (fun x _ y _ hneq ↦ single_single_commute hneq (f x) (f y))

@[simp]
theorem noncommProd_singleQubit (f : Fin n → 𝐔[Qubit]) (s : Finset (Fin n)) :
    s.noncommProd (fun i ↦ single i (f i)) (by simp) = ⨂ i, if (i ∈ s) then f i else 1 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha IH =>
    have (i : Fin n) : (if i = a ∨ i ∈ s then f i else 1) =
        (if i = a then f a else 1) * (if i ∈ s then f i else 1) := by grind
    simp_rw [Finset.noncommProd_cons, IH, Finset.cons_eq_insert, Finset.mem_insert, this,
    ← mul_piKroneckerUnitary_mul, single_eq_prod]


