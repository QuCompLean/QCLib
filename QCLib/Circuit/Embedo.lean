/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import QCLib.Circuit.Gate.Bipartite
public import QCLib.Logic.Equiv
public import QCLib.LinearAlgebra.OuterProduct
public import QCLib.LinearAlgebra.UnitaryGroup.Kronecker
public import QCLib.Logic.Equiv
public import QCLib.LinearAlgebra.Unitary

/-!

# Embedding unitary gates into larger systems

## Main Definitions

* `single i U` : The embedding of a unitary matrix `U : 𝐔[k]` into `𝐔[ι → k]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices.

* `bipartite i j U` : The embedding of a unitary matrix `U : U[k × k]` into `𝐔[ι → k]`
realized by acting with `U` on the `i`th and the `j`th index, and trivially on all other indices.

For the dependent case, use `single'` and `bipartite'`.

-/


@[expose] public noncomputable section

open Function PiOuterProduct OuterProduct Equiv Matrix UnitaryGroup

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {k : ι → Type*} [∀ i, DecidableEq (k i)] [∀ i, Fintype (k i)]

namespace Unitary

/-- The embedding of a unitary matrix `U : 𝐔[k i]` into `𝐔[Π i, k i]` realized by
acting with `U` on the `i`-th factor, and trivially on all other indices. -/
@[simps! coe]
def single' (i : ι) (U : 𝐔[k i]) : 𝐔ᶠ[Π i, k i] :=
  toUnitaryEuclideanCLM
    (reindexMonoidEquiv (Equiv.piSplitAt i k).symm
      (blockDiagonalMonoidHom (fun _ ↦ U)))
