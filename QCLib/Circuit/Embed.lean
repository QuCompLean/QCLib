module

public import QCLib.Circuit.Gate.BiPartite
public import QCLib.LinearAlgebra.PiOuterProduct.Equiv
public import QCLib.LinearAlgebra.UnitaryGroup.Kronecker


@[expose] public section

open Matrix UnitaryGroup Fin Function PiOuterProduct

variable {n}

section single

/-- Single qubit gate acting on register -/
@[simps!]
def singleQubit (i : Fin n) (U : 𝐔[Qubit]) := ⨂ j, if j = i then U else 1

theorem singleQubit_def (U : 𝐔[Qubit]) (i : Fin n) :
  singleQubit i U = ⨂ j, if j = i then U else 1 := by rfl

@[simps!]
def singleQubitBlock (i : Fin (n + 1)) (U : 𝐔[Qubit]) : 𝐔[Register (n + 1)] :=
  reindexMonoidEquiv (insertNthEquiv _ i) (blockDiagonalMonoidHom (fun _ => U))

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

end single

section two

@[simps!]
def twoQubit (i j : Fin n) (U : 𝐔[Qubit × Qubit]) (h : j ≠ i := by grind) : 𝐔[Register n] :=
  (reindexMonoidEquiv (funSplitTwo i j h (l := Qubit)).symm) (blockDiagonalMonoidHom (fun _ => U))

theorem twoQubit_apply_apply (A : 𝐔[Qubit × Qubit])
    (i j : Fin n) (h : j ≠ i := by decide) (a b : Register n) :
    twoQubit i j A h a b =
      if ∀ k, k ≠ i → k ≠ j → a k = b k then A (a i, a j) (b i, b j) else 0 := by
  simp [blockDiagonal_apply, funext_iff]

@[simp]
theorem twoQubit_apply_basis (A : 𝐔[Qubit × Qubit]) (i j : Fin n) (h : j ≠ i) (v : Register n) :
    twoQubit i j A h • δ[v] = ∑ q, A q (v i, v j) • δ[update (update v i q.1) j q.2] := by
  ext w
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, twoQubit_apply_apply, one_smul, Finset.sum_apply,
    Pi.single_apply, smul_eq_mul, funext_iff, update_apply]
  split_ifs
  · rw [Finset.sum_eq_single (w i, w j)] <;> grind
  · rw [Finset.sum_eq_zero]; grind

@[simp]
theorem twoQubit_diagonal (d : Qubit × Qubit → unitary ℂ) (i j : Fin n) (h : j ≠ i) :
    twoQubit i j (diagonalMonoidHom d) h = diagonalMonoidHom fun k ↦ d (k i, k j) := by
  ext
  simp [diagonal_apply, funext_iff]
  grind

set_option backward.isDefEq.respectTransparency false in
theorem twoQubitGateAt_kronecker (A B : 𝐔[Qubit]) (i j : Fin n) (h : j ≠ i) :
    twoQubit i j (A ⊗ᵤ B) h = ⨂ k, if k = i then A else if k = j then B else 1 := by
  ext k l
  simp only [twoQubit_apply_apply, ne_eq, coe_piKroneckerUnitary, piKronecker_apply]
  split_ifs with h
  · have (i : Fin n) : Finset.card {x | x = i} = 1 := Finset.card_eq_one.mpr (by use i; grind)
    push_cast
    simp_rw [apply_ite Subtype.val, ite_apply _]
    simp_all [Finset.prod_ite]
  · obtain ⟨w, hw⟩ := not_forall.mp h
    refine (Finset.prod_eq_zero (Finset.mem_univ w) ?_).symm
    simp_all

@[simp]
theorem controllize_of_zero {n} (U : 𝐔[Qubit]) (i j : Fin n) (h : j ≠ i)
    (v : Register n) (hv : v j = 0) : twoQubit i j C[U] h • δ[v] = δ[v] := by
  ext w
  by_cases hw : v = w
  all_goals
    simp_all [basisVector_def, Submonoid.smul_def, funext_iff, blockDiagonal_apply,
      Pi.single_apply, Matrix.one_apply]
    try grind

@[simp]
theorem controllize_of_one {n : ℕ} (U : 𝐔[Qubit]) (i j : Fin n.succ) (h : j ≠ i)
    (v : Register n.succ) (hv : v j = 1) :
    twoQubit i j C[U] h • δ[v] = ∑ q, U q (v i) • δ[(Function.update v i q)] := by
  ext w
  by_cases hw : v = w
  all_goals
    simp_all [basisVector_def, Submonoid.smul_def, funext_iff, blockDiagonal_apply,
      Pi.single_apply]
    grind

end two
