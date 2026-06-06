/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Qml.Matrix.PiKronecker.Unitary

@[expose] public section

open Module Matrix PiTensorProduct
open scoped TensorProduct

variable {ι : Type}

variable {R : Type} [CommSemiring R]
variable {l m n : Type}
variable {M : Type} [AddCommMonoid M] [Module R M]
variable {N : Type} [AddCommMonoid N] [Module R N]
variable (b : ι → Basis n R M) (b' : ι → Basis n R N)

-- TBD: Currently stated for non-dependent case.

-- Unapplied version of `Basis.piTensorProduct_repr_tprod_apply`
-- We can now state it, because we there's now a definition of a tensor product of vectors.
/-- The basis representation of the tensor product of a vector is the tensor
product of the basis representations. -/
theorem Basis.piTensorProduct_repr_tprod [Fintype ι] (b : Π _ : ι, Basis n R M)
    (x : Π _ : ι, M) :
    (Basis.piTensorProduct b).repr (⨂ₜ[R] i, x i) = ⨂ᵥ i, (b i).repr (x i) := by
  ext p
  simp

/-- The basis representation of a tensor product of linear maps is the Kronecker
product of their basis representations. -/
theorem LinearMap.toMatrix_piTensorProduct_map_eq_kroneckerProduct
    [DecidableEq ι] [Fintype ι] [DecidableEq n] [Fintype n] (f : Π _ : ι,  M →ₗ[R] N) :
    LinearMap.toMatrix (Basis.piTensorProduct b) (Basis.piTensorProduct b') (PiTensorProduct.map f)
      = ⨂ₖ i, LinearMap.toMatrix (b i) (b' i) (f i) := by
  ext
  simp [LinearMap.toMatrix_apply] -- why is `LinearMap.toMatrix_apply` not a simp lemma?
