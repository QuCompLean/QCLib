module

public import QCLib.LinearAlgebra.StdBasis
public import QCLib.LinearAlgebra.Unitary
public import QCLib.LinearAlgebra.UnitaryGroup.RootsOfUnity

@[expose] public noncomputable section

open Unitary Matrix

variable (d : ℕ)

attribute [simp ←] map_pow

notation "𝐔ᶠ["n"]" => unitary (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)

theorem orderOf_finRotate [hd : d.AtLeastTwo] :
    orderOf (finRotate d) = d := by
  simp [(isCycle_finRotate_of_le hd.prop).orderOf, support_finRotate_of_le hd.prop]


def Z : 𝐔ᶠ[Fin d] := diagonalMonoidHom (fun k => (uζ d) ^ (k : ℕ))

def X : 𝐔ᶠ[Fin d] := permHom (finRotate d)

@[simp]
theorem Z_apply (k : Fin d) : (Z d) δ[k] = ((uζ d) ^ (k : ℕ)) • δ[k] := by
  ext
  simp [Z, basisVector_def, Submonoid.smul_def]
  grind

@[simp]
theorem X_apply (k : Fin d) [NeZero d] : (X d) δ[k] = δ[(k + 1)] := by
  ext
  simp [X, basisVector_def, permHom_apply, UnitaryGroup.toUnitaryEuclideanCLM_coe]
  grind

@[simp]
theorem Z_pow [NeZero d] : (Z d) ^ d = 1 := by
  ext
  simp [Z, pow_right_comm]

@[simp]
theorem X_pow [hd : d.AtLeastTwo] : (X d) ^ d = 1 := by
  simp [X, ((orderOf_eq_iff hd.toNeZero.pos).mp (orderOf_finRotate d)).left]

theorem orderOf_Z [hd : d.AtLeastTwo] : orderOf (Z d) = d :=
  (orderOf_eq_iff hd.toNeZero.pos).mpr (by
    simp only [Z_pow, ne_eq, true_and]
    intro m hmd hm hz
    apply ((orderOf_eq_iff hd.toNeZero.pos).mp (orderOf_uζ d)).right m hmd hm
    rw [Z, ← diagonalMonoidHom_one, ← map_pow,
      Function.Injective.eq_iff diagonalMonoidHom_injective] at hz
    simpa [Nat.mod_eq_of_lt hd.one_lt] using congrFun hz 1
  )

-- theorem orderOf_X [hd : d.AtLeastTwo] : orderOf (X d) = d :=
--   (orderOf_eq_iff hd.toNeZero.pos).mpr (by
--     simp only [X_pow, ne_eq, true_and]
--     intro m hmd hm hx
--     simp [X, permHom] at hx
--     apply_fun Subtype.val at hx
--     apply_fun ContinuousLinearMap.toLinearMap at hx
--     have := LinearMap.congr_fun hx 0
--     rw [ContinuousLinearMap.coe_coe, map_zero, OneMemClass.coe_one,
--       ContinuousLinearMap.coe_one, Module.End.one_apply] at this
--     sorry
--   )
