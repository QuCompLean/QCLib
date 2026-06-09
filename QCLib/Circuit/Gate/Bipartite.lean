/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import QCLib.LinearAlgebra.UnitaryGroup.Permutation
public import QCLib.LinearAlgebra.UnitaryGroup.Kronecker
public import QCLib.Tactic.MatrixExpand


/-!

# Bipartite Qubit gates

Gates acting on two subsystems.

## Main definitions

* `controllize n U` : The controlled-`U` gate. For `U : 𝐔[k]`, return the unitary in `𝐔[Fin n × k]`
that applies `U ^ x` to the second subsystem if the first system is in state `x`.

* `controllizeRight n U` : For `U : 𝐔[k]`, return the unitary in `𝐔[k × Fin n]` that
applies `U ^ x` to the first subsystem if the second system is in state `x`.

* `Swap` : The unitary that exchanges two subsytems.

## Notation

* `C[U]` for `controllize 2 U`
* `[U]C` for `controllizeRight 2 U`

## Implementation notes

The order used by `controllize` is more common in quantum information applications, but
`controllizeRight` is easier to define in terms of `Matrix.blockDiagonal`. Hence we start
with `controllizeRight` and derive properties of `controllize` from those of `controllizeRight`
where possible.

-/

public section Controllize

variable {k} [Fintype k] [DecidableEq k]

variable (n : ℕ)

open Matrix.UnitaryGroup Matrix

/-- For `U : 𝐔[k]`, return the unitary in `𝐔[k × Fin n]` that applies `U ^ x` to the first
subsystem if the second system is in state `x`. -/
@[simps! coe, expose]
def controllizeRight (U : 𝐔[k]) : 𝐔[k × Fin n] := blockDiagonalStarMonoidHom fun k ↦ U ^ (k.toNat)

theorem controllizeRight_def (U : 𝐔[k]) :
  controllizeRight n U = blockDiagonalStarMonoidHom fun k ↦ U ^ (k.toNat) := by rfl

@[simp]
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

-- TBD: Left version
theorem controllizeRight_conj (U V : 𝐔[k]) :
    controllizeRight n (V * U * V⁻¹) = (V ⊗ᵤ 1) * controllizeRight n U * (V ⊗ᵤ 1)⁻¹  := by
  ext
  simp [controllizeRight_def, ← diagonal_one, kronecker_diagonal]

/-- The controlled-`U` gate. For `U : 𝐔[k]`, return the unitary in `𝐔[Fin n × k]` that
applies `U ^ x` to the second subsystem if the first system is in state `x`. -/
@[simps! coe, expose]
def controllize (U : 𝐔[k]) : 𝐔[Fin n × k] :=
  (reindexMonoidEquiv (Equiv.prodComm k (Fin n))) (controllizeRight n U)

theorem controllize_def (U : 𝐔[k]) :
    controllize n U  = (reindexMonoidEquiv (Equiv.prodComm k (Fin n))) (controllizeRight n U) := by
  rfl

-- TBD: Intro def for `reindexMonoidEquiv (Equiv.prodComm k n))` and state more generally?
theorem controllize_eq_controllizeRight_swap (U : 𝐔[k]) (a b : Fin n × k) :
    controllize n U a b = controllizeRight n U a.swap b.swap := by
  simp [controllize_def]

theorem controllize_one : controllize n (1 : 𝐔[k]) = 1 := by
  simp [controllize_def]

theorem controllize_zpow (U : 𝐔[k]) (p : ℤ) : (controllize n U) ^ p =  controllize n (U ^ p) := by
  simp_rw [controllize_def, ← map_zpow, controllizeRight_zpow]

theorem controllize_diagonal (d : k → unitary ℂ) :
    controllize n (diagonalMonoidHom d) = diagonalMonoidHom fun x ↦ (d x.2) ^ (x.1.toNat) := by
  ext
  simp [controllize_def, controllizeRight_diagonal, diagonal_apply]

namespace Qubit

/- Notation for controllized gates where the controlling system is a qubit -/
notation "[" g "]C" => controllizeRight 2 g
notation "C[" g "]" => controllize 2 g

theorem controllizeRight_mul (g₁ g₂ : 𝐔[k]) : [g₁]C * [g₂]C = [g₁ * g₂]C := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  fin_cases i₂, j₂ <;> simp [controllizeRight, ← blockDiagonal_mul, blockDiagonal_apply]

theorem controllize_mul (g₁ g₂ : 𝐔[k]) : C[g₁] * C[g₂] = C[g₁ * g₂] := by
  simp [controllize, ← map_mul, controllizeRight_mul]

@[simp]
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

@[simp]
theorem controllize_apply (U : 𝐔[k]) (a b : Qubit × k) :
    C[U] a b =
    if a.1 = b.1 then
      if a.1 = 0 then
        (1 : 𝐔[k]) (a.2) (b.2)
      else
        U (a.2) (b.2)
    else 0 := by
  simp [controllize_eq_controllizeRight_swap]

end Qubit

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
