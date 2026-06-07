/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Gross
-/

module


public import Qml.Circuits.MultiQubit


@[expose] public noncomputable section

open Complex Qubit Braket Matrix

open scoped Matrix Braket

theorem X_apply_ket {k : Qubit} : X • ‖k⟩ = ‖(k+1)⟩ := by
  fin_cases k <;> matrix_expand [basisVector_def]

theorem Z_apply_ket {k : Qubit} : Z • ‖k⟩ = (-1 : ℂ) ^ (k : ℕ) • ‖k⟩ := by
  fin_cases k <;> matrix_expand [basisVector_def]

abbrev upKet := ∣up⟩
abbrev dnKet := ∣dn⟩
abbrev plsKet := ∣pls⟩
abbrev mnsKet := ∣mns⟩

example : upKet = ‖(0 : Qubit)⟩ := by simp only [upKet, up]
example : dnKet = ‖(1 : Qubit)⟩ := by simp only [dnKet, dn]
example : ‖(0 : Qubit)⟩ + ‖(1 : Qubit)⟩ = ∣(up + dn)⟩ := ket_plus_ket ..

def PhiPls' : Matrix (Register 2) (Fin 1) ℂ := (√2)⁻¹ • (‖![0, 0]⟩ + ‖![1,1]⟩)
def PhiMns' : Matrix (Register 2) (Fin 1) ℂ := (√2)⁻¹ • (‖![0, 0]⟩ - ‖![1,1]⟩)
def PsiPls' : Matrix (Register 2) (Fin 1) ℂ := (√2)⁻¹ • (‖![0, 1]⟩ + ‖![1,0]⟩)
def PsiMns' : Matrix (Register 2) (Fin 1) ℂ := (√2)⁻¹ • (‖![0, 1]⟩ - ‖![1,0]⟩)

def IX := ⨂ₖ i, ![1, X] i
def IY := ⨂ₖ i, ![1, Y] i
def IZ := ⨂ₖ i, ![1, Z] i

--- `matrix_expand` does work for these, but it's very slow.

theorem iY_PhiPls_eq_I_PsiMns' : IY • PhiPls' = I • PsiMns' := by
  matrix_expand [IY, Y_eq, PhiPls', PsiMns', basisVector_def]

theorem iZ_PhiPls_eq_PhiMns' : IZ • PhiPls' = PhiMns' := by
  matrix_expand [IZ, Z_eq, PhiPls', PhiMns', basisVector_def]


/-- Computational basis kets factorize -/
theorem basisKet_eq_prod {n : ℕ} (k : Register n) : ‖k⟩ = ⨂ₖ i, ‖(k i)⟩ := by
  ext
  simp [basisVector_def, Pi.single_eq_prod]
