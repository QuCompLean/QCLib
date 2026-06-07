module

public import QCLib.LinearAlgebra.UnitaryGroup.Basic
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.Lemmas
public import QCLib.Circuit.Gate.Qubit


public section Controllize

variable {k} [Fintype k] [DecidableEq k]

open Matrix.UnitaryGroup Matrix

@[simps! coe, expose]
def controllize (U : 𝐔[k]) : 𝐔[k × Qubit] := blockDiagonalStarMonoidHom ![1, U]

notation "C[" g "]" => controllize g

theorem controllize_diagonal (d : Qubit → unitary ℂ) : C[diagonalMonoidHom d] =
    diagonalMonoidHom fun k ↦ if k.2 = 1 then d k.1 else 1 := by
  ext i j
  fin_cases i, j <;> simp [blockDiagonal_apply]

theorem controllize_diagonal_pow (d : Qubit → unitary ℂ) :
    C[diagonalMonoidHom d] = diagonalMonoidHom fun k ↦ (d k.1) ^ (k.2 : ℕ) := by
  ext i j
  fin_cases i, j <;> simp [blockDiagonal_apply]

@[simp]
theorem controllize_mul (g₁ g₂ : 𝐔[k]) : C[g₁] * C[g₂] = C[g₁ * g₂] := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₂, j₂ <;> simp [← blockDiagonal_mul, blockDiagonal_apply]

@[simp]
theorem controllize_one : C[(1 : 𝐔[k])] = 1 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₂, j₂ <;> simp [blockDiagonal_apply, Matrix.one_apply]
