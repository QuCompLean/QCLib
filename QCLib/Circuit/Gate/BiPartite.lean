module

public import QCLib.LinearAlgebra.UnitaryGroup.Basic
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.Lemmas
public import QCLib.Circuit.Gate.Qubit

/-!

# Bipartite Qubit gates

Gates acting on two subsystems.

`controllize U` : Applies unitary gate `U` to the first subsytem, if the second subsytem (a `Qubit`)
is in `1` state. Otherwise it applies identity.

`Swap` : Exchanges two subsytems.

-/

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

@[simp]
theorem controllize_mul_inv (g : 𝐔[k]) : C[g] * C[g⁻¹] = 1 := by
  simp

end Controllize



public section Swap

open Matrix.UnitaryGroup Matrix

def Swap : 𝐔[Qubit × Qubit] :=
  ⟨of fun a b => ite (a = b.swap) 1 0, by
    rw [mem_unitaryGroup_iff]
    matrix_expand
  ⟩

@[matrixExpand]
theorem swap_eq :
  Swap.val = of fun a b => ite (a = b.swap) 1 0 := by rfl

@[simp] theorem swap_swap : Swap * Swap = 1 := by
  matrix_expand

@[simp]
theorem swap_apply {a b} :
    Swap a b = ite (a = b.swap) 1 0 := by
  simp [swap_eq]

@[simp]
theorem swap_apply_basis {v : Qubit × Qubit} :
    Swap • δ[v] = δ[v.swap] := by
  matrix_expand

end Swap
