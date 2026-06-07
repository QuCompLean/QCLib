module

public import QCLib.LinearAlgebra.UnitaryGroup.Basic
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.Lemmas
public import QCLib.Circuit.Gate.Qubit



public section single

open Matrix UnitaryGroup Fin Function

variable {n}

@[simps!, expose]
def singleQubit (i : Fin (n + 1)) (U : 𝐔[Qubit]) : 𝐔[Register (n + 1)] :=
  reindexMonoidEquiv (insertNthEquiv _ i)
    (UnitaryGroup.blockDiagonalMonoidHom (fun _ => U))

@[simp]
lemma prod_ind_flatten (i) (a b : Register (n + 1)) :
    (a i = b i ∧ i.removeNth a = i.removeNth b) ↔ a = b := by
  refine ⟨fun h => ?_ , fun h => by simp_all⟩
  rw [← Fin.insertNth_self_removeNth i a, ← Fin.insertNth_self_removeNth i b, h.1, h.2]

@[simp]
theorem singleQubit_diagonal (d : Qubit → unitary ℂ) (i : Fin (n + 1)) :
    singleQubit i (diagonalMonoidHom d) = diagonalMonoidHom fun k ↦ d (k i) := by
  ext
  simp [diagonal_apply]

/- No longer a simp lemma. `singleQubit_coe` must be excluded
  from the simp call before applying this lemma -/
theorem singleQubit_apply_apply (U : 𝐔[Qubit]) (i : Fin (n + 1)) (a b : Register (n + 1)) :
    singleQubit i U a b = if ∀ k ≠ i, a k = b k then U (a i) (b i) else 0 := by
  simp [blockDiagonal_apply, Fin.removeNth_apply,
    funext_iff, Fin.succAbove_ne, Fin.forall_iff_succAbove i]

-- TBD : old proof, use blockDiagonal properties
theorem singleQubit_apply_basis {n} (v : Register (n + 1)) (j : Fin (n + 1)) (U : 𝐔[Qubit]) :
    singleQubit j U • δ[v] = ∑ q, U q (v j) • δ[update v j q] := by
  ext k
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, singleQubit_apply_apply, one_smul,
    Finset.sum_apply, Pi.single_apply, smul_eq_mul, funext_iff, update_apply]
  split_ifs
  · rw [Finset.sum_eq_single (k j)] <;> grind
  · rw [Finset.sum_eq_zero]; grind






-- section

-- variable {α γ β : Type*} (v₁ : α → γ) (v₂ : β → γ)

-- /-- simplify? -/
-- def outerProd [Mul γ] : α × β → γ :=
--   uncurry (of.symm vecMulVec v₁ v₂)

-- infixl:100 " ⊗ᵥ " => outerProd

-- @[simp]
-- theorem outerProd_apply [Mul γ] (i) : (v₁ ⊗ᵥ v₂) i = v₁ i.1 * v₂ i.2 := by rfl

-- @[simp]
-- theorem zero_outerProd [MulZeroClass γ] : (0 : α → γ) ⊗ᵥ v₂ = 0 := by
--   ext
--   simp

-- @[simp]
-- theorem outerProd_zero [MulZeroClass γ] : v₁ ⊗ᵥ (0 : β → γ) = 0 := by
--   ext
--   simp

-- @[simp]
-- theorem add_outerProd [Mul γ] [Add γ] [RightDistribClass γ] (v₁ v₂ : α → γ) (w : β → γ) :
--     (v₁ + v₂) ⊗ᵥ w = (v₁ ⊗ᵥ w) + v₂ ⊗ᵥ w := by
--   ext
--   simp [add_mul]

-- @[simp]
-- theorem outerProd_add [Mul γ] [Add γ] [LeftDistribClass γ] (v₁ v₂ : α → γ) (w : β → γ) :
--     w ⊗ᵥ (v₁ + v₂) = (w ⊗ᵥ v₁) + w ⊗ᵥ v₂ := by
--   ext
--   simp [mul_add]


-- lemma basisVector_insertNth (v : Register (n + 1)) (j : Fin (n + 1)) :
--     δ[v] ∘ (insertNthEquiv _ j) = δ[v j] ⊗ᵥ δ[j.removeNth v] := by
--   ext ⟨a, b⟩
--   simp [outerProd_apply, basisVector_def, Pi.basisFun_apply, Pi.single_apply, insertNthEquiv,
--           Fin.insertNth_eq_iff]
--   grind

-- theorem singleQubit_apply_basis'
--       (v : Register (n + 1)) (j : Fin (n + 1)) (U : 𝐔[Qubit]) :
--     singleQubit j U • δ[v] =
--       (U • δ[v j]) ⊗ᵥ δ[j.removeNth v] ∘ (insertNthEquiv _ j).symm := by
--   ext k
--   by_cases hk : k = v
--   · simp [hk, Submonoid.smul_def, basisVector_def]
--   · simp [Submonoid.smul_def, basisVector_def, blockDiagonal_apply]
--     split_ifs <;> simp_all
-- end
