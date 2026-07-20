module

public import QCLib.LinearAlgebra.StdBasis
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import QCLib.LinearAlgebra.UnitaryGroup.RootsOfUnity

public section

open Unitary

notation "𝐔ᶠ["n"]" => unitary (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)

noncomputable def Z (d) : 𝐔ᶠ[Fin d] := diagonalMonoidHom (fun i => uζ i)
