import QCLib.Tactic.MatrixExpand
import Mathlib

notation "𝐔[" t "]" => Matrix.unitaryGroup t ℂ

abbrev Qubit := Fin 2
abbrev Register (n : Nat) := Fin n → Qubit

def Z : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, -1], by simp only [Matrix.mem_unitaryGroup_iff]; matrix_expand⟩

def X : 𝐔[Qubit] :=
  ⟨!![0, 1; 1, 0], by simp only [Matrix.mem_unitaryGroup_iff]; matrix_expand⟩

/-- Reindex `Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ` to `Matrix (Register 2) (Register 2) ℂ`. -/
def indexEquiv : Qubit × Qubit ≃ Register 2 := (finTwoArrowEquiv Qubit).symm
-- indexEquiv requires the piFinList function in the tactic definition to work.

def IX : Matrix (Register 2) (Register 2) ℂ :=
  Matrix.reindex indexEquiv indexEquiv (Matrix.kroneckerMap (· * ·) 1 X.val)

def IZ : Matrix (Register 2) (Register 2) ℂ :=
  Matrix.reindex indexEquiv indexEquiv (Matrix.kroneckerMap (· * ·) 1 Z.val)

noncomputable def PhiPls' : Register 2 → ℂ :=
  (√2)⁻¹ • (Pi.single (![0, 0] : Register 2) 1 + Pi.single (![1, 1] : Register 2) 1)

noncomputable def PsiPls' : Register 2 → ℂ :=
  (√2)⁻¹ • (Pi.single (![0, 1] : Register 2) 1 + Pi.single (![1, 0] : Register 2) 1)

local notation:100 M " ⬝ᵥ " v => Matrix.mulVec M v

-- matrix_neq works with piFinList vectors/matrices
example : (IX ⬝ᵥ PhiPls') ≠ PhiPls' := by
  matrix_neq [IX, PhiPls', X, PsiPls', indexEquiv]

example : (IZ ⬝ᵥ  PhiPls') ≠ PhiPls' := by
  matrix_neq [IZ, Z, PsiPls', PhiPls', indexEquiv]

-- matrix_neq also works with normal matrices
example : X ≠ 1 := by
  matrix_neq [X]


example : X ≠ 1 := by
  matrix_neq
-- One can check the infoview to get a better look what the tactic does under the hood
  simp [X] at h_1

-- Testing matrix_exp_at_hyp as a standalone tactic
example (θ : ℝ) (ψ : Fin 2 → ℂ)
    (hrot : (Matrix.of ![![(Real.cos θ : ℂ), -(Real.sin θ : ℂ)],
    ![(Real.sin θ : ℂ), (Real.cos θ : ℂ)]]).mulVec ψ = ![1, 0]) :
    (Real.cos θ : ℂ) * ψ 0 - (Real.sin θ : ℂ) * ψ 1 = 1 := by
  matrix_exp_at_hyp at hrot
