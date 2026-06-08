module

public import QCLib.LinearAlgebra.UnitaryGroup.Basic
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.Lemmas
public import QCLib.Circuit.Gate.Qubit
public import QCLib.LinearAlgebra.UnitaryGroup.Permutation -- needed?

/-!

# Bipartite Qubit gates

Gates acting on two subsystems.

## Main definitions

* `controllize U` : The controlled-`U` gate. Applies the unitary gate `U` to the
  second subsytem, if the first subsytem (which must be a `Qubit`) is in the `1` state.
  Otherwise it applies identity.

* `controllizeRight U` : Applies the unitary gate `U` to the
  first subsytem, if the second subsytem (which must be a `Qubit`) is in the `1` state.
  Otherwise it applies identity.

* `Swap` : Exchanges two subsytems.

## Main results

## Implementation notes

The order used by `controllize` is more common, but `controllizeRight` is easier
to define in terms of `Matrix.blockDiagonal`. Hence we start with
`controllizeRight` and derive properties of `controllize` from those of
`controllizeRight` where possible.

-/

public section Controllize

variable {k} [Fintype k] [DecidableEq k]

open Matrix.UnitaryGroup Matrix

/-- The controlled-`U` gate, with the second factor controlling the application
of `U` on the first factor . -/
@[simps! coe, expose]
def controllizeRight (U : 𝐔[k]) : 𝐔[k × Qubit] := blockDiagonalStarMonoidHom ![1, U]

notation "[" g "]C" => controllizeRight g

theorem controllizeRight_diagonal (d : Qubit → unitary ℂ) : [diagonalMonoidHom d]C =
    diagonalMonoidHom fun k ↦ if k.2 = 1 then d k.1 else 1 := by
  ext i j
  fin_cases i, j <;> simp [blockDiagonal_apply]

theorem controllizeRight_diagonal_pow (d : Qubit → unitary ℂ) :
    [diagonalMonoidHom d]C = diagonalMonoidHom fun k ↦ (d k.1) ^ (k.2 : ℕ) := by
  ext i j
  fin_cases i, j <;> simp [blockDiagonal_apply]

@[simp]
theorem controllizeRight_mul (g₁ g₂ : 𝐔[k]) : [g₁]C * [g₂]C = [g₁ * g₂]C := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₂, j₂ <;> simp [← blockDiagonal_mul, blockDiagonal_apply]

@[simp]
theorem controllizeRight_one : [(1 : 𝐔[k])]C = 1 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₂, j₂ <;> simp [blockDiagonal_apply, Matrix.one_apply]

-- remove?
theorem controllizeRight_mul_inv (g : 𝐔[k]) : [g]C * [g⁻¹]C = 1 := by
  simp


/-- The controlled-`U` gate. -/
@[expose]
def controllize (U : 𝐔[k]) : 𝐔[Qubit × k] := (reindexMonoidEquiv (Equiv.prodComm k Qubit)) [U]C

notation "C[" g "]" => controllize g

@[simp]
theorem controllize_def (U : 𝐔[k]) :
  C[U] = (reindexMonoidEquiv (Equiv.prodComm k Qubit)) [U]C := rfl

theorem controllize_diagonal (d : Qubit → unitary ℂ) : C[diagonalMonoidHom d] =
    diagonalMonoidHom fun k ↦ if k.1 = 1 then d k.2 else 1 := by
  ext i j
  fin_cases i, j <;> simp [blockDiagonal_apply]

theorem controllize_diagonal_pow (d : Qubit → unitary ℂ) :
    C[diagonalMonoidHom d] = diagonalMonoidHom fun k ↦ (d k.2) ^ (k.1 : ℕ) := by
  ext i j
  fin_cases i, j <;> simp [blockDiagonal_apply]

@[simp]
theorem controllize_mul (g₁ g₂ : 𝐔[k]) : C[g₁] * C[g₂] = C[g₁ * g₂] := by
  simp [← map_mul]

@[simp]
theorem controllize_one : C[(1 : 𝐔[k])] = 1 := by
  simp

@[simp]
theorem controllize_mul_inv (g : 𝐔[k]) : C[g] * C[g⁻¹] = 1 := by
  simp [← map_mul]

end Controllize

public section Swap

open Matrix.UnitaryGroup Matrix

/-- Swap gate as an explicit matrix. -/
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
