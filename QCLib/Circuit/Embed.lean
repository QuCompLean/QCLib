module

public import QCLib.LinearAlgebra.UnitaryGroup.Basic
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.Lemmas
public import QCLib.Circuit.Gate.Qubit
public import QCLib.Mathlib.LinearAlgebra.PiOuterProduct


@[expose] public section single

open Matrix UnitaryGroup Fin Function PiOuterProduct

variable {n}


/-- Single qubit gate acting on register -/
@[simps!]
def singleQubit (i : Fin n) (U : 𝐔[Qubit]) := ⨂ j, if j = i then U else 1

theorem singleQubit_def (U : 𝐔[Qubit]) (i : Fin n) :
  singleQubit i U = ⨂ j, if j = i then U else 1 := by rfl

@[simps!]
def singleQubitBlock (i : Fin (n + 1)) (U : 𝐔[Qubit]) : 𝐔[Register (n + 1)] :=
  reindexMonoidEquiv (insertNthEquiv _ i)
    (UnitaryGroup.blockDiagonalMonoidHom (fun _ => U))

@[simp]
lemma prod_ind_flatten (i) (a b : Register (n + 1)) :
    (a i = b i ∧ i.removeNth a = i.removeNth b) ↔ a = b := by
  refine ⟨fun h => ?_ , fun h => by simp_all⟩
  rw [← Fin.insertNth_self_removeNth i a, ← Fin.insertNth_self_removeNth i b, h.1, h.2]

theorem singleQubitBlock_apply_apply (U : 𝐔[Qubit]) (i : Fin (n + 1)) (a b : Register (n + 1)) :
    singleQubitBlock i U a b = if ∀ k ≠ i, a k = b k then U (a i) (b i) else 0 := by
  simp [blockDiagonal_apply, Fin.removeNth_apply,
    funext_iff, Fin.succAbove_ne, Fin.forall_iff_succAbove i]

theorem singleQubit_eq_singleQubitBlock (U) (i : Fin (n + 1)) :
    singleQubit i U = singleQubitBlock i U := by
  ext a b
  simp only [singleQubit_coe, piKronecker_apply, singleQubitBlock_apply_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single i] <;> aesop
  · obtain ⟨w, hw⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by simp_all)

@[simp]
theorem singleQubit_apply_apply (U : 𝐔[Qubit]) (i : Fin n) (a b : Register n) :
    singleQubit i U a b = if ∀ k ≠ i, a k = b k then U (a i) (b i) else 0 := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => rw [singleQubit_eq_singleQubitBlock, singleQubitBlock_apply_apply]

@[simp]
theorem singleQubit_diagonal (d : Qubit → unitary ℂ) (i : Fin n) :
    singleQubit i (diagonalMonoidHom d) = diagonalMonoidHom fun k ↦ d (k i) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n => ext; simp [singleQubit_eq_singleQubitBlock, diagonal_apply]

-- TBD: old proof, use blockDiagonal properties
theorem singleQubit_apply_basis {n} (v : Register n) (j : Fin n) (U : 𝐔[Qubit]) :
    singleQubit j U • δ[v] = ∑ q, U q (v j) • δ[update v j q] := by
  ext k
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, singleQubit_apply_apply, one_smul,
    Finset.sum_apply, Pi.single_apply, smul_eq_mul, funext_iff, update_apply]
  split_ifs
  · rw [Finset.sum_eq_single (k j)] <;> grind
  · rw [Finset.sum_eq_zero]; grind

-- TBD: Maybe define a general notion of `support`? State for more general situations
@[simp]
theorem single_single_commute {n : ℕ} {i j : Fin n} (h : i ≠ j) (U V : 𝐔[Qubit]) :
    Commute (singleQubit i U) (singleQubit j V) := by
  simp only [singleQubit_def, commute_iff_eq, mul_piKroneckerUnitary_mul]
  congr
  grind
