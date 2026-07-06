import Mathlib
import QCLib.Mathlib.LinearAlgebra.PiOuterProduct

open scoped PiOuterProduct

variable {ι : Type*} [Fintype ι]

variable {l : ι → Type*} [∀ i, Fintype (l i)]

-- family of vectors in an Euclidean space
variable {f : (i : ι) → EuclideanSpace ℂ (l i)}

instance : PiOuterProduct (fun i ↦ EuclideanSpace ℂ (l i)) (EuclideanSpace ℂ (Π i, l i)) where
  tprod := fun f ↦ WithLp.toLp 2 (⨂ i, ((f i) : (l i → ℂ)))
