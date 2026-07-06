import Mathlib
import QCLib.Mathlib.LinearAlgebra.PiOuterProduct

open scoped PiOuterProduct

variable {ι : Type*} [Fintype ι]

variable {l : ι → Type*} [∀ i, Fintype (l i)]

-- family of vectors in an Euclidean space
variable {f : (i : ι) → EuclideanSpace ℂ (l i)}

instance : PiOuterProduct (fun i ↦ EuclideanSpace ℂ (l i)) (EuclideanSpace ℂ (Π i, l i)) where
  tprod f := WithLp.toLp 2 (⨂ i, ((f i) : (l i → ℂ)))


#synth SMul (Matrix (Fin 2) (Fin 2) ℂ) (EuclideanSpace ℂ (Fin 2))

#synth SMul (Matrix.unitaryGroup (Fin 2) ℂ) (EuclideanSpace ℂ (Fin 2))

variable (M : Matrix.unitaryGroup (Fin 2) ℂ) (v : EuclideanSpace ℂ (Fin 2))

#check M • v -- `M • v : EuclideanSpace ℂ (Fin 2)`

#check Metric.sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1

#synth SMul (Matrix.unitaryGroup (Fin 2) ℝ) ((Metric.sphere (0 : (EuclideanSpace ℝ (Fin 2))) 1))

#check HSMul
#check SMul
