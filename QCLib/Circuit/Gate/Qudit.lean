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

def X : 𝐔ᶠ[Fin d] := permHom ℂ (finRotate d)

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

@[simp]
theorem orderOf_Z [hd : d.AtLeastTwo] : orderOf (Z d) = d :=
  (orderOf_eq_iff hd.toNeZero.pos).mpr (by
    simp only [Z_pow, ne_eq, true_and]
    intro m hmd hm h
    apply ((orderOf_eq_iff hd.toNeZero.pos).mp (orderOf_uζ d)).right m hmd hm
    rw [Z, ← diagonalMonoidHom_one, ← map_pow,
      Function.Injective.eq_iff diagonalMonoidHom_injective] at h
    simpa [Nat.mod_eq_of_lt hd.one_lt] using congrFun h 1
  )

@[simp]
theorem orderOf_X [hd : d.AtLeastTwo] : orderOf (X d) = d :=
  (orderOf_eq_iff hd.toNeZero.pos).mpr (by
    simp only [X_pow, ne_eq, true_and]
    intro m hmd hm h
    apply ((orderOf_eq_iff hd.toNeZero.pos).mp (orderOf_finRotate d)).right m hmd hm
    apply permHom_injective
    simpa [X] using h
  )

theorem Z_X_anticomm [hd : NeZero d] : (Z d) * (X d) = (uζ d) • (X d) * (Z d) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  apply ContinuousLinearMap.ext_basis_iff.mp (fun i ↦ ?_)
  simp [← pow_succ', Fin.val_add_one]
  aesop (add safe simp ((orderOf_eq_iff (by simp)).mp (orderOf_uζ (n + 1))))
