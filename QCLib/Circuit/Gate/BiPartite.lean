module

public import QCLib.LinearAlgebra.UnitaryGroup.Permutation
public import QCLib.Tactic.MatrixExpand


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

## Notation

* `C[U]` for `controllize U`
* `[U]C` for `controllizeRight U`

## Implementation notes

The order used by `controllize` is more common, but `controllizeRight` is easier
to define in terms of `Matrix.blockDiagonal`. Hence we start with
`controllizeRight` and derive properties of `controllize` from those of
`controllizeRight` where possible.

-/

public section Controllize

variable {k} [Fintype k] [DecidableEq k]

variable (n : ℕ)

open Matrix.UnitaryGroup Matrix

def controllizeRight (U : 𝐔[k]) : 𝐔[k × Fin n] := blockDiagonalStarMonoidHom fun k ↦ U ^ (k.toNat)

theorem controllizeRight_def (U : 𝐔[k]) :
  controllizeRight n U = blockDiagonalStarMonoidHom fun k ↦ U ^ (k.toNat) := by rfl

theorem controllizeRight_one : controllizeRight n (1 : 𝐔[k]) = 1 := by
  simp [controllizeRight_def, ← Pi.one_def]

theorem controllizeRight_zpow (U : 𝐔[k]) (p : ℤ) :
    (controllizeRight n U) ^ p =  controllizeRight n (U ^ p) := by
  simp only [controllizeRight_def, ← map_zpow, Fin.toNat_eq_val]
  congr
  ext1
  rw [Pi.pow_apply, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]

theorem controllizeRight_inv (U : 𝐔[k]) : (controllizeRight n U)⁻¹ =  controllizeRight n (U⁻¹) := by
  simp_rw [← _root_.zpow_neg_one, controllizeRight_zpow]

theorem controllizeRight_diagonal (d : k → unitary ℂ) :
    controllizeRight n (diagonalMonoidHom d) = diagonalMonoidHom fun x ↦ (d x.1) ^ (x.2.toNat) := by
  apply Subtype.ext
  simp [controllizeRight_def, diagonal_pow]


theorem controllizeRight'_eq_controllizeRight (U : 𝐔[Qubit]) : controllizeRight' U = [U]C := by
  simp only [controllizeRight', Fin.toNat_eq_val, controllizeRight]
  congr
  ext k
  fin_cases k <;> simp

@[simp]
theorem controllizeRight'_mul (g₁ g₂ : 𝐔[k]) :
  (controllizeRight' (n := n) g₁) * controllizeRight' g₂ = controllizeRight' (g₁ * g₂) := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₂, j₂ <;>
  · simp [controllizeRight']
    simp [← blockDiagonal_mul]
    congr
    ext l
    simp [← mul_pow]
    simp [← pow_mul]







    simp [controllizeRight', ← blockDiagonal_mul, blockDiagonal_apply]

@[simp]
theorem controllizeRight_one : [(1 : 𝐔[k])]C = 1 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₂, j₂ <;> simp [blockDiagonal_apply, Matrix.one_apply]




end ControllizeTest


/-- The controlled-`U` gate, with the second factor controlling the application
of `U` on the first factor . -/
@[simps! coe, expose]
def controllizeRight (U : 𝐔[k]) : 𝐔[k × Qubit] := blockDiagonalStarMonoidHom ![1, U]

notation "[" g "]C" => controllizeRight g

@[simp]
theorem controllizeRight_mul (g₁ g₂ : 𝐔[k]) : [g₁]C * [g₂]C = [g₁ * g₂]C := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₂, j₂ <;> simp [← blockDiagonal_mul, blockDiagonal_apply]

theorem controllizeRight_diagonal (d : Qubit → unitary ℂ) :
    [diagonalMonoidHom d]C = diagonalMonoidHom fun k ↦ if k.2 = 1 then d k.1 else 1 := by
  ext i j
  fin_cases i, j <;> simp [blockDiagonal_apply]

theorem controllizeRight_diagonal_pow (d : Qubit → unitary ℂ) :
    [diagonalMonoidHom d]C = diagonalMonoidHom fun k ↦ (d k.1) ^ (k.2 : ℕ) := by
  ext i j
  fin_cases i, j <;> simp [blockDiagonal_apply]


@[simp]
theorem controllizeRight_one : [(1 : 𝐔[k])]C = 1 := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₂, j₂ <;> simp [blockDiagonal_apply, Matrix.one_apply]

theorem controllizeRight_mul_inv (g : 𝐔[k]) : [g]C * [g⁻¹]C = 1 := by
  simp

theorem controllizeRight_apply (U : 𝐔[k]) (a b : k × Qubit) :
   [U]C a b =
    if a.2 = b.2 then
      if a.2 = 0 then
        (1 : 𝐔[k]) (a.1) (b.1)
      else
        U (a.1) (b.1)
    else 0 := by
  simp only [controllizeRight_coe, blockDiagonal_apply, Fin.isValue, OneMemClass.coe_one]
  generalize h : a.2 = c
  fin_cases c <;> simp

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

theorem controllize_apply (U : 𝐔[k]) (a b : Qubit × k) :
    C[U] a b =
    if a.1 = b.1 then
      if a.1 = 0 then
        (1 : 𝐔[k]) (a.2) (b.2)
      else
        U (a.2) (b.2)
    else 0 := by
  simp only [controllize_def, reindexMonoidEquiv_apply_coe, controllizeRight_coe,
    Equiv.prodComm_symm, Equiv.coe_prodComm, submatrix_apply, blockDiagonal_apply, Prod.snd_swap,
    Prod.fst_swap, Fin.isValue, OneMemClass.coe_one]
  generalize h : a.1 = c
  fin_cases c <;> simp

end Controllize

public section Swap

open Matrix.UnitaryGroup Matrix

variable {n} [Fintype n] [DecidableEq n]

/-- The swap gate. -/
def Swap : 𝐔[n × n] := permHom ℂ (Equiv.prodComm n n)


-- Missing simp lemma?
@[simp]
theorem Equiv.prodComm_prodComm {n : Type*} : (Equiv.prodComm n n) * (Equiv.prodComm n n) = 1 := by
  ext <;> simp

@[simp]
theorem swap_swap : Swap * Swap = (1 : 𝐔[n × n]) := by
  simp [Swap, ← map_mul]

@[simp]
theorem swap_apply_apply {a b : n × n} : Swap a b = if a = b.swap then 1 else 0 := by
  simp [Swap]
  grind

@[matrixExpand]
theorem swap_coe :
  (Swap (n := n) : Matrix (n × n) (n × n) ℂ) = of fun a b : n × n ↦ ite (a = b.swap) 1 0 := by
  ext
  simp

@[simp]
theorem swap_apply_basis {v : n × n} : Swap (n := n) • δ[v] = δ[v.swap] := by
  simp [Swap]

-- needed?
abbrev QubitSwap := Swap (n := Qubit)

end Swap
