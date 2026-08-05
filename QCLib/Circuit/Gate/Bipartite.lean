/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import QCLib.LinearAlgebra.Unitary
public import QCLib.LinearAlgebra.OuterProduct

/-!

# Bipartite qudit gates

Gates acting on two subsystems.

## Main definitions

* `controllize n U` : The controlled-`U` gate. For `U : 𝐔ᶠ[k]`, return the unitary in
`𝐔ᶠ[Fin n × k]` that applies `U ^ x` to the second subsystem if the first system is in state `x`.

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

public noncomputable section Controllize

variable {k} [Fintype k] [DecidableEq k]

variable (n : ℕ)

open Unitary.EuclideanCLM OuterProduct

/-- For `U : 𝐔[k]`, return the unitary in `𝐔[k × Fin n]` that applies `U ^ x` to the first
subsystem if the second system is in state `x`. -/
@[simps! coe, expose]
def controllizeRight (U : 𝐔ᶠ[k]) : 𝐔ᶠ[k × Fin n] :=
  blockDiagonalStarMonoidHom fun k ↦ U ^ (k.toNat)

theorem controllizeRight_def (U : 𝐔ᶠ[k]) :
  controllizeRight n U = blockDiagonalStarMonoidHom fun k ↦ U ^ (k.toNat) := by rfl

@[simp]
theorem controllizeRight_one : controllizeRight n (1 : 𝐔ᶠ[k]) = 1 := by
  simp [controllizeRight_def, ← Pi.one_def, -blockDiagonalStarMonoidHom_coe]

theorem controllizeRight_zpow (U : 𝐔ᶠ[k]) (p : ℤ) :
    (controllizeRight n U) ^ p =  controllizeRight n (U ^ p) := by
  simp only [controllizeRight_def, ← map_zpow, Fin.toNat_eq_val]
  congr
  ext1
  rw [Pi.pow_apply, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast]

theorem controllizeRight_inv (U : 𝐔ᶠ[k]) :
    (controllizeRight n U)⁻¹ =  controllizeRight n (U⁻¹) := by
  simp_rw [← _root_.zpow_neg_one, controllizeRight_zpow]

theorem controllizeRight_diagonal (d : k → unitary ℂ) :
    controllizeRight n (diagonalMonoidHom d) =
      diagonalMonoidHom fun x ↦ (d x.1) ^ (x.2.toNat) := by
  apply Subtype.ext
  simp [controllizeRight_def, Matrix.diagonal_pow, diagonalMonoidHom_coe]

-- TBD: Left version
open Matrix in
theorem controllizeRight_conj (U V : 𝐔ᶠ[k]) :
    controllizeRight n (V * U * V⁻¹) =
      (V ⨂ (1 : 𝐔ᶠ[Fin n])) * controllizeRight n U * (V ⨂ (1 : 𝐔ᶠ[Fin n]))⁻¹ := by
  ext
  simp [controllizeRight_def, ← Matrix.diagonal_one, Matrix.kronecker_diagonal]

/-- The controlled-`U` gate. For `U : 𝐔ᶠ[k]`, return the unitary in `𝐔ᶠ[Fin n × k]` that
applies `U ^ x` to the second subsystem if the first system is in state `x`. -/
@[simps! coe, expose]
def controllize (U : 𝐔ᶠ[k]) : 𝐔ᶠ[Fin n × k] :=
  (reindexMonoidEquiv (Equiv.prodComm k (Fin n))) (controllizeRight n U)

theorem controllize_def (U : 𝐔ᶠ[k]) :
    controllize n U  = (reindexMonoidEquiv (Equiv.prodComm k (Fin n))) (controllizeRight n U) := by
  rfl

-- Move out
@[simps!, expose]
noncomputable def EuclideanSpace.swap {q k : Type*} [Fintype q] [Fintype k] [DecidableEq q]
    [DecidableEq k] {𝕜 : Type*} [RCLike 𝕜] :
    EuclideanSpace 𝕜 (q × k) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (k × q) :=
  LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 (Equiv.prodComm q k)

@[simp]
theorem EuclideanSpace.swap_ofLp_apply {k : Type*} [Fintype k]
    [DecidableEq k] {𝕜 : Type*} [RCLike 𝕜] (a : EuclideanSpace 𝕜 (Fin n × k)) :
  (EuclideanSpace.swap a).ofLp = (fun x ↦ a.ofLp x.swap) := rfl

attribute [simp] Matrix.submatrix_mulVec_equiv
-- One of special cases that working with CLMs makes the proof counterintuitively harder
-- TBD: Intro def for `reindexMonoidEquiv (Equiv.prodComm k n))` and state more generally?
theorem controllize_eq_controllizeRight_swap (U : 𝐔ᶠ[k])
    (a : EuclideanSpace ℂ (Fin n × k)) (b : Fin n × k) :
    controllize n U a b = controllizeRight n U a.swap b.swap := by
  simp [controllize_def, -Equiv.coe_prodComm, Function.comp_def]
