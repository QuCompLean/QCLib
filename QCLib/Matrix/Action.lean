/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.Data.Matrix.Action

/-!
# Some actions of matrices

Action of non-square matrices on vectors.

## To do

Better documentation of rationale.
-/

@[expose] public section

open Matrix

section SMulHRight

variable {n m l : Type*} [Fintype m]
variable {α : Type v} [CommSemiring α]

instance Matrix.instHSMulMat : HSMul (Matrix n m α) (Matrix m l α) (Matrix n l α) where
  hSMul a b := a * b

-- For matrices, this is redundant, but this one should get picked up for the `unitaryGroup`.
instance Matrix.instSMulMat : SMul (Matrix m m α) (Matrix m l α) where
  smul a b := a * b

@[simp]
theorem Matrix.hsmul_def (A : Matrix n m α) (B : Matrix m l α) : A • B = A * B := rfl

instance (priority := 900) Matrix.instHSMulVec : HSMul (Matrix n m α) (m → α) (n → α) where
  hSMul A v := A *ᵥ v

@[simp]
theorem Matrix.smul_vec_def (A : Matrix n m α) (v : m → α) : A • v = A *ᵥ v := rfl

end SMulHRight
