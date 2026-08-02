/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import QCLib.LinearAlgebra.UnitaryGroup.Permutation
public import QCLib.LinearAlgebra.UnitaryGroup.Kronecker
public import QCLib.Tactic.MatrixExpand
public import QCLib.LinearAlgebra.Unitary

/-!

# Bipartite Qudit gates

Gates acting on two subsystems.

## Main definitions

* `controllize n U` : The controlled-`U` gate. For `U : 𝐔ᶠ[k]`, return the unitary in
`𝐔ᶠ[Fin n × k]` that applies `U ^ x` to the second subsystem if the first system is in state `x`.

* `controllizeRight n U` : For `U : 𝐔ᶠ[k]`, return the unitary in `𝐔ᶠ[k × Fin n]` that
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

public noncomputable section Controllize

variable {k} [Fintype k] [DecidableEq k]

variable (n : ℕ)

open Matrix UnitaryGroup

/-- For `U : 𝐔ᶠ[k]`, return the unitary in `𝐔ᶠ[k × Fin n]` that applies `U ^ x` to the first
subsystem if the second system is in state `x`. -/
@[simps! coe, expose]
def controllizeRight (U : 𝐔[k]) : 𝐔ᶠ[k × Fin n] :=
  euclideanCLMEquiv (blockDiagonalStarMonoidHom fun k ↦ U ^ (k.toNat))

theorem controllizeRight_def (U : 𝐔[k]) :
    controllizeRight n U =
    euclideanCLMEquiv (blockDiagonalStarMonoidHom fun k ↦ U ^ (k.toNat)) := by
  rfl

@[simp]
theorem controllizeRight_one : controllizeRight n (1 : 𝐔[k]) = 1 := by
  ext
  simp [controllizeRight_def, ← Pi.one_def]

theorem controllizeRight_zpow (U : 𝐔[k]) (p : ℤ) :
    (controllizeRight n U) ^ p =  controllizeRight n (U ^ p) := by
  simp only [controllizeRight_def, ← map_zpow, Fin.toNat_eq_val]
  congr
  ext1
  rw [Pi.pow_apply, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]

theorem controllizeRight_inv (U : 𝐔[k]) :
    (controllizeRight n U)⁻¹ = controllizeRight n (U⁻¹) := by
  simp_rw [← _root_.zpow_neg_one, controllizeRight_zpow]

theorem controllizeRight_diagonal (d : k → unitary ℂ) :
    controllizeRight n (diagonalMonoidHom d) =
      Unitary.diagonalMonoidHom fun x ↦ (d x.1) ^ (x.2.toNat) := by
  ext
  simp [controllizeRight_def, diagonal_pow, mulVec_diagonal]

-- -- TBD: Left version
-- theorem controllizeRight_conj (U V : 𝐔[k]) :
--     controllizeRight n (V * U * V⁻¹) = (V ⊗ᵤ 1) * controllizeRight n U * (V ⊗ᵤ 1)⁻¹  := by
--   ext
--   simp [controllizeRight_def, ← diagonal_one, kronecker_diagonal]
