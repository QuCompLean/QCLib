/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import QCLib.LinearAlgebra.UnitaryGroup.RootsOfUnity
public import QCLib.LinearAlgebra.StdBasis
public import QCLib.Misc.OrderOf

import QCLib.Misc.IntCast

/-!

# Single qubit gates

..many small definitions, partly based on @timeroot's repo.

## To do

Very slow, mainly due to use of `matrix_expand`.

-/

public section

open Real Complex

namespace Qubit

open Matrix

-- ## Some single-qubit gates

/-- The Pauli Z gate on a qubit. -/
def Z : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, -1], by simp only [Matrix.mem_unitaryGroup_iff]; matrix_expand⟩

/-- The Pauli X gate on a qubit. -/
def X : 𝐔[Qubit] :=
  ⟨!![0, 1; 1, 0], by simp only [Matrix.mem_unitaryGroup_iff]; matrix_expand⟩

-- Avoid?
/-- The Pauli Y gate on a qubit. -/
def Y : 𝐔[Qubit] :=
  ⟨!![0, -I; I, 0], by simp only [Matrix.mem_unitaryGroup_iff]; matrix_expand⟩

@[matrixExpand]
theorem Z_eq : Z.val = !![1, 0; 0, -1] := by rfl

@[matrixExpand]
theorem X_eq : X.val = !![0, 1; 1, 0] := by rfl

@[matrixExpand]
theorem Y_eq : Y.val = !![0, -I; I, 0] := by rfl

/-- The H gate, a Hadamard gate, on a qubit. -/
noncomputable def H : 𝐔[Qubit] :=
  ⟨(√(1/2) : ℂ) • (!![1, 1; 1, -1]), by rw [Matrix.mem_unitaryGroup_iff]; matrix_expand⟩

/-- The S gate, or Rz(π/2) rotation on a qubit. -/
def S : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, I], by rw [Matrix.mem_unitaryGroup_iff]; matrix_expand⟩

set_option warn.sorry false in
-- `simp` and `ring_nf` don't agree on `(√2)⁻¹` as normal form
example (c : ℂ) : 1/√2 = c := by
  simp
  ring_nf
  sorry

/-- The T gate, or Rz(π/4) rotation on a qubit. -/
noncomputable def T : 𝐔[Qubit] :=
  ⟨!![1, 0; 0, (√2)⁻¹ * (1 + I)], by rw [Matrix.mem_unitaryGroup_iff]; matrix_expand⟩

noncomputable def R (k : ℕ) : 𝐔[Qubit] := ⟨!![1, 0; 0, ζ (2^k)], by
  rw [Matrix.mem_unitaryGroup_iff]
  matrix_expand
  ⟩

@[matrixExpand]
theorem H_eq : H.val = (√(1/2) : ℂ) • !![1, 1; 1, -1] := by rfl

@[matrixExpand]
theorem S_eq : S.val = !![1, 0; 0, I] := by rfl

@[matrixExpand]
theorem T_eq : T.val = !![1, 0; 0, (√2)⁻¹ * (1 + I)] := by rfl

@[matrixExpand]
theorem R_eq (k : ℕ) : R k = !![1, 0; 0, ζ (2^k)] := by rfl

@[simp]
theorem Z_sq : Z * Z = 1 := by
  matrix_expand

@[simp]
theorem orderOf_Z_eq_two : orderOf Z = 2 :=
    orderOf_eq_prime (by simp) (by matrix_neq [Z])

@[simp]
theorem X_sq : X * X = 1 := by
  matrix_expand

@[simp]
theorem orderOf_X_eq_two : orderOf X = 2 :=
    orderOf_eq_prime (by simp) (by matrix_neq [X])

@[simp]
theorem Y_sq : Y * Y = 1 := by
  matrix_expand

@[simp]
theorem orderOf_Y_eq_two : orderOf Y = 2 :=
    orderOf_eq_prime (by simp) (by matrix_neq [Y])

@[simp]
theorem H_sq : H * H = 1 := by
  matrix_expand

@[simp]
theorem orderOf_H_eq_two : orderOf H = 2 :=
    orderOf_eq_prime (by simp) (by matrix_neq [H])

@[simp]
theorem S_sq : S * S = Z := by
  matrix_expand

@[simp]
theorem orderOf_S_eq_four : orderOf S = 4 :=
    orderOf_prime_pow_root' (show orderOf Z = 2 ^ 1 by simp) (show S ^ 2 = Z by simp [sq])

@[simp]
theorem T_sq : T * T = S := by
  matrix_expand [T, S]

@[simp]
theorem orderOf_T_eq_eight : orderOf T = 8 :=
    orderOf_prime_pow_root' (show orderOf S = 2 ^ 2 by simp) (show T ^ 2 = S by simp [sq])

-- Alphabetical order as simp normal form

@[simp]
theorem Y_X_anticomm : Y * X = -(X * Y) := by
  matrix_expand

@[simp]
theorem Z_Y_anticomm : Z * Y = -(Y * Z) := by
  matrix_expand

@[simp]
theorem Z_X_anticomm : Z * X = -(X * Z) := by
  matrix_expand

@[simp]
theorem X_Y_eq : X * Y = ᵤI • Z := by
  matrix_expand [u_I_eq_I]

theorem X_Z_eq : X * Z = -ᵤI • Y := by
  matrix_expand [u_I_eq_I]

@[simp]
theorem Y_Z_eq : Y * Z = ᵤI • X := by
  matrix_expand [u_I_eq_I]

@[simp]
theorem Y_zpow_X_zpow_anticomm (p q : ℤ) : Y ^ p * X ^ q = (ᵤ-1) ^ (p * q) • X ^ q * Y ^ p := by
  cases Int.even_or_odd q <;> cases Int.even_or_odd p <;> simp_all

@[simp]
theorem Z_zpow_Y_zpow_anticomm (p q : ℤ) : Z ^ p * Y ^ q = (ᵤ-1) ^ (p * q) • Y ^ q * Z ^ p := by
  cases Int.even_or_odd q <;> cases Int.even_or_odd p <;> simp_all

@[simp]
theorem Z_zpow_X_zpow_anticomm (p q : ℤ) : Z ^ p * X ^ q = (ᵤ-1)^(p * q) • X^q * Z^p := by
  cases q.even_or_odd <;> cases Int.even_or_odd p <;> simp_all

@[simp]
theorem H_mul_X_eq_Z_mul_H : H * X = Z * H := by
  matrix_expand

@[simp]
theorem H_mul_Z_eq_X_mul_H : H * Z = X * H := by
  matrix_expand

@[simp]
theorem H_conj_Z : H * Z * H⁻¹ = X := by
  simp

@[simp]
theorem H_conj_Z_zpow (z : ℤ) : H * Z ^ z * H⁻¹ = X ^ z := by
  rw [← H_conj_Z]
  exact conj_zpow.symm

@[simp]
theorem S_Z_comm : Z * S = S * Z := by
  simp [← S_sq, mul_assoc]

@[simp]
theorem T_Z_comm : Z * T = T * Z := by
  simp [← S_sq, ← T_sq, mul_assoc]

@[simp]
theorem S_T_comm : S * T = T * S := by
  simp [← T_sq, mul_assoc]

-- ## Properties

theorem X_hermitian : IsHermitian (X : Matrix Qubit Qubit ℂ) := by
  matrix_expand

theorem Y_hermitian : IsHermitian (Y : Matrix Qubit Qubit ℂ) := by
  matrix_expand

theorem Z_hermitian : IsHermitian (Z : Matrix Qubit Qubit ℂ) := by
  matrix_expand

@[simp]
theorem X_det : det (X : Matrix Qubit Qubit ℂ) = -1 := by
  simp [X, det_fin_two]

@[simp]
theorem Y_det : det (Y : Matrix Qubit Qubit ℂ) = -1 := by
  simp [Y, det_fin_two]

@[simp]
theorem Z_det : det (Z : Matrix Qubit Qubit ℂ) = -1 := by
  simp [Z]

@[simp]
theorem X_trace : trace (X :  Matrix Qubit Qubit ℂ) = 0 := by
  simp [X]

@[simp]
theorem XZ_trace : trace (X * Z :  Matrix Qubit Qubit ℂ) = 0 := by
  simp [X, Z]

@[simp]
theorem Y_tr : trace Y.val = 0 := by
  simp [Y]

@[simp]
theorem Z_trace : trace (Z :  Matrix Qubit Qubit ℂ) = 0 := by
  simp [Z]

-- TBD: Fix performance issues, probably at `push_cast`.
@[simp]
theorem Z_zpow_trace (p : ℤ) : trace (Z^p :  Matrix Qubit Qubit ℂ) = if Even p then 2 else 0 := by
  rcases p.even_or_odd with h | h <;>
  · have := congrArg (↑· : 𝐔[Qubit] → Matrix Qubit Qubit ℂ) (h.zpow_of_sq Z_sq)
    push_cast at this
    simp [h, this]

@[simp]
theorem X_zpow_trace (p : ℤ) : trace (X^p :  Matrix Qubit Qubit ℂ) = if Even p then 2 else 0 := by
  rcases p.even_or_odd with h | h <;>
  · have := congrArg (↑· : 𝐔[Qubit] → Matrix Qubit Qubit ℂ) (h.zpow_of_sq X_sq)
    push_cast at this
    simp [h, this]

@[simp]
theorem X_zpow_Z_zpow_trace (p q : ℤ) : trace ((X ^ q * Z ^ p) : Matrix Qubit Qubit ℂ) =
    if Even p ∧ Even q then 2 else 0 := by
  rcases p.even_or_odd with hp | hp <;> rcases q.even_or_odd with hq | hq <;>
  · have hZ := congrArg (↑· : 𝐔[Qubit] → Matrix Qubit Qubit ℂ) (hp.zpow_of_sq Z_sq)
    have hX := congrArg (↑· : 𝐔[Qubit] → Matrix Qubit Qubit ℂ) (hq.zpow_of_sq X_sq)
    simp only [Matrix.UnitaryGroup.coe_zpow] at hZ hX -- push_cast is very slow
    simp_all

theorem Z_diagonal : Z = Matrix.UnitaryGroup.diagonalMonoidHom fun k : Qubit ↦ (-1) ^ (k : ℕ) := by
  matrix_expand
-- TBD: keep one?
theorem Z_diagonal' : Z = Matrix.UnitaryGroup.diagonalMonoidHom fun k : Qubit ↦ (-1) ^ (k : ℤ) := by
  matrix_expand

-- ## Some single-qubit states

-- Vectors

open Matrix

-- Unexpose?
@[expose] noncomputable section

def up : (Qubit → ℂ) := δ[0]
def dn : (Qubit → ℂ) := δ[1]
def pls : (Qubit → ℂ) := ((√2)⁻¹ : ℂ) • (δ[0] + δ[1])
def mns : (Qubit → ℂ) := ((√2)⁻¹ : ℂ) • (δ[0] - δ[1])
def lft : (Qubit → ℂ) := ((√2)⁻¹ : ℂ) • (δ[0] + I • δ[1])
def rgt : (Qubit → ℂ) := ((√2)⁻¹ : ℂ) • (δ[0] - I • δ[1])

end

example : pls = (√2)⁻¹ • ![1, 1] := by matrix_expand [pls]
example : mns = (√2)⁻¹ • ![1, -1] := by matrix_expand [mns]
example : lft = (√2)⁻¹ • ![1, I] := by matrix_expand [lft]
example : rgt = (√2)⁻¹ • ![1, -I] := by matrix_expand [rgt]

/-
# Actions
-/

open scoped Fin.IntCast

section ActionOnBasis

variable (k : Fin 2)

@[simp]
theorem X_apply : X • δ[k] = δ[(k + 1)] := by
  fin_cases k <;> matrix_expand

@[simp]
theorem Z_apply : Z • δ[k] = (-1 : ℂ)^(k : ℕ) • δ[k] := by
  fin_cases k <;> matrix_expand

@[simp]
theorem Z_coe_apply (k l : Fin 2) : Z.val k l = if k = l then if k = 0 then 1 else -1 else 0 := by
  fin_cases k <;> fin_cases l <;> simp [Z]


@[simp]
theorem H_apply : H • δ[k] = ((√2)⁻¹ : ℂ) • (δ[0] + (-1 : ℂ)^(k : ℕ) • δ[1]) := by
  fin_cases k <;> matrix_expand

@[simp]
theorem S_apply :
    S • δ[k] = I ^ (k : ℕ) • δ[k] := by
  fin_cases k <;> matrix_expand

@[simp]
theorem T_apply :
    T • δ[k] = ((√2)⁻¹ * (1 + I)) ^ (k : ℕ) • δ[k] := by
  fin_cases k <;> matrix_expand

@[simp]
theorem R_apply (n) (k : Qubit) : R n • δ[k] = (ζ (2 ^ n)) ^ (k : ℕ) • δ[k] := by
  fin_cases k <;> matrix_expand

end ActionOnBasis

-- Can prove the special case via `matrix_expand`
@[simp]
theorem Z_pls_eq_mns : Z • pls = mns := by
  matrix_expand [pls, mns, basisVector_def]
-- It'd be cleaner to deduce if from the general fact...
-- ...but it takes some fiddling to get the arithmetic right.
example : Z • pls = mns := by
  calc
    _ = ((√2)⁻¹ : ℂ) • (Z • δ[(0 : Qubit)] + Z • δ[1]) := by rw [pls, smul_comm, smul_add]
    _ = ((√2)⁻¹ : ℂ) • (δ[(0 : Qubit)] - δ[1]) := by simp [Z_apply, sub_eq_add_neg]
--
example : Z • pls = mns := by
  rw [pls, mns, smul_comm, smul_add]
  simp [Z_apply, sub_eq_add_neg]

@[simp]
theorem Z_mns_eq_pls : Z • mns = pls := by
  rw [← inv_eq_of_mul_eq_one_right Z_sq]
  exact ((smul_eq_iff_eq_inv_smul Z).mp Z_pls_eq_mns).symm

@[simp]
theorem H_up_eq_plus : H • δ[(0 : Fin 2)] = pls := by
  matrix_expand [up, pls]

section IntCast

open scoped Fin.IntCast

variable (k : Fin 2)

@[simp]
theorem X_zpow_apply (q : ℤ) : X^q • δ[k] = δ[(k + ↑q)] := by
  rcases q.even_or_odd with h | h <;> simp [h.zpow_of_sq X_sq, h.intCast_fin_two]

@[simp]
theorem Z_zpow_apply (q : ℤ) : Z^q • δ[k] = (-1 : ℂ) ^ (q * k) • δ[k] := by
  rcases q.even_or_odd with h | h <;> fin_cases k <;> simp [h.zpow_of_sq Z_sq, h.neg_one_zpow]

@[simp]
theorem Z_zpow_pls (p : ℤ) : Z^p • pls = ((√2)⁻¹ : ℂ) • (δ[(0 : Qubit)] + (-1 : ℂ)^p • δ[1]) := by
  rcases p.even_or_odd with h | h
  · simp [h, pls]
  · simp [h.zpow_of_sq Z_sq, h.neg_one_zpow, mns, sub_eq_add_neg]

@[simp]
theorem Z_pow_pls (p : ℕ) : Z^p • pls = ((√2)⁻¹ : ℂ) • (δ[(0 : Qubit)] + (-1 : ℂ)^p • δ[1]) := by
  simpa only [zpow_natCast] using Z_zpow_pls p

end IntCast

end Qubit
