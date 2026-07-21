module

public import QCLib.LinearAlgebra.StdBasis
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import QCLib.LinearAlgebra.UnitaryGroup.RootsOfUnity

@[expose] public noncomputable section

open Unitary

variable (d : ℕ)

attribute [simp ←] map_pow

notation "𝐔ᶠ["n"]" => unitary (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)

def Z : 𝐔ᶠ[Fin d] := diagonalMonoidHom (fun k => (uζ d) ^ (k : ℕ))

@[simp]
theorem Z_pow [NeZero d] : (Z d) ^ d = 1 := by
  ext
  simp [Z, pow_right_comm]

theorem orderOf_Z [hd : d.AtLeastTwo] : orderOf (Z d) = d :=
  (orderOf_eq_iff hd.toNeZero.pos).mpr (by
    simp only [Z_pow, ne_eq, true_and]
    intro m hmd hm hz
    apply ((orderOf_eq_iff hd.toNeZero.pos).mp (orderOf_uζ d)).right m hmd hm
    rw [Z, ← Unitary.diagonalMonoidHom_one, ← map_pow,
      Function.Injective.eq_iff Unitary.diagonalMonoidHom_injective] at hz
    simpa [Nat.mod_eq_of_lt hd.one_lt] using congrFun hz 1
  )
