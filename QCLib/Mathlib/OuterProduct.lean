/-
Copyright (c) 2026 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/

module

public import QCLib.LinearAlgebra.Unitary

@[expose] public section

/-
# Binary Outer Product

Binary outer/kronecker product for many types makes sense:
`Pi`, `Matrix`, `unitaryGroup`, (with basis: `E →ₗ[R] M`, `E →L[R] M`, `unitary (E →L[R] M)`), etc.
This file defines a `OuterProduct` notation typeclass to unify all notations.

## Definition

* `OuterProductMap f r s` is the pointwise outer product of the functions
  `r` and `s`. Its value at `(i, j)` is `f (r i) (s j)`.

## Naming convention
We will use the spelling `OuterProduct` for functions / vectors and `KroneckerProduct` for matrices
and `TensorProduct` for linearmaps.

## Implementation notes

`Matrix.vecMulVec` already provides an outer product operation for `Pi`, but its
result is a matrix rather than a tuple-indexed function.

-/

/-- Notation typeclass for `a ⨂ b`. The binary analogue of `PiOuterProduct`. -/
class OuterProduct (α β : Type*) (γ : outParam Type*) where
  tprod : α → β → γ

-- `TensorProduct` uses ⨂ as opposed to ⨂.
@[inherit_doc OuterProduct]
scoped[OuterProduct] infixr:70 " ⨂ " => OuterProduct.tprod

open scoped OuterProduct

namespace Pi

variable {α β γ M : Type*} (f : γ → γ → γ) (r : α → γ) (s : β → γ)

/-- Given a binary operation `f`, `OuterProductMap f r s` is the pointwise outer
product of the functions `r` and `s`. Its value at `(i, j)` is `f (r i) (s j)`.
the usual binary tensor product of functions is given via `OuterProductMap` instance. -/
def OuterProductMap : α × β → γ :=
  fun ⟨i, j⟩ ↦ f (r i) (s j)

@[simp]
theorem OuterProductMap_apply (i : α) (j : β) :
    OuterProductMap f r s (i, j) = f (r i) (s j) := by rfl

instance [Mul γ] : OuterProduct (α → γ) (β → γ) (α × β → γ) where
  tprod := OuterProductMap (· * · : γ → γ → γ)

@[simp]
theorem outerProduct_apply [Mul γ] (i : α) (j : β) :
    (r ⨂ s) (i, j) = r i * s j := by rfl

@[simp]
theorem zero_outerProduct [MulZeroClass γ] : (0 : α → γ) ⨂ s = 0 := by
  ext ⟨i, j⟩; simp

@[simp]
theorem outerProduct_zero [MulZeroClass γ] : r ⨂ (0 : β → γ) = 0 := by
  ext ⟨i, j⟩; simp

@[simp]
theorem add_outerProduct [Mul γ] [Add γ] [RightDistribClass γ] (r s : α → γ) (w : β → γ) :
    (r + s) ⨂ w = (r ⨂ w) + s ⨂ w := by
  ext ⟨i, j⟩; simp [add_mul]

@[simp]
theorem outerProduct_add [Mul γ] [Add γ] [LeftDistribClass γ] (r s : α → γ) (w : β → γ) :
    w ⨂ (r + s) = (w ⨂ r) + w ⨂ s := by
  ext ⟨i, j⟩; simp [mul_add]

-- Weaken assumptions on `γ`?
theorem sum_outerProduct [CommRing γ] (w : β → γ)
    {ι : Type*} (S : Finset ι) (f : ι → (α → γ)) :
    (∑ i ∈ S, f i) ⨂ w = ∑ i ∈ S, f i ⨂ w := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => simp_all

theorem outerProduct_sum [CommRing γ] (r : α → γ)
    {ι : Type*} (S : Finset ι) (f : ι → (β → γ)) :
    r ⨂ (∑ i ∈ S, f i) = ∑ i ∈ S, r ⨂ f i := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => simp_all

@[simp]
theorem smul_outerProduct [Mul γ] [SMul M γ] [IsScalarTower M γ γ] (c : M) :
    (c • r) ⨂ s = c • (r ⨂ s) := by
  ext ⟨i, j⟩; simp [smul_mul_assoc]

@[simp]
theorem outerProduct_smul [Mul γ] [SMul M γ] [SMulCommClass M γ γ] (c : M) :
    r ⨂ (c • s) = c • (r ⨂ s) := by
  ext ⟨i, j⟩; simp [mul_smul_comm]

@[simp]
theorem outerProduct_smul_smul [Mul γ] [Monoid M] [MulAction M γ]
    [IsScalarTower M γ γ] [SMulCommClass M γ γ] (c d : M) :
    (c • r) ⨂ (d • s) = (d * c) • (r ⨂ s) := by
  rw [outerProduct_smul, smul_outerProduct, smul_smul]

@[simp]
theorem neg_outerProduct [Mul γ] [HasDistribNeg γ] :
    (-r) ⨂ s = -(r ⨂ s) := by
  ext ⟨i, j⟩; simp [neg_mul]

@[simp]
theorem outerProduct_neg [Mul γ] [HasDistribNeg γ] :
    r ⨂ (-s) = -(r ⨂ s) := by
  ext ⟨i, j⟩; simp [mul_neg]

theorem outerProduct_left_injective
    [MulZeroClass γ] [IsRightCancelMulZero γ] (hs : s ≠ 0) :
    Function.Injective (fun r : α → γ => r ⨂ s) := by
  intro r r' h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hs
  ext i
  have h' := congrArg (fun f => f (i, j)) h
  simp_all

theorem outerProduct_right_injective
    [MulZeroClass γ] [IsLeftCancelMulZero γ] (hr : r ≠ 0) :
    Function.Injective (fun s : β → γ => r ⨂ s) := by
  intro s s' h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hr
  ext j
  have h' := congrArg (fun f => f (i, j)) h
  simp_all

def outerProductBilinearMap [CommSemiring γ] :
    (α → γ) →ₗ[γ] (β → γ) →ₗ[γ] (α × β → γ) :=
  LinearMap.mk₂ γ (· ⨂ ·) (by simp) (by simp) (by simp) (by simp)

end Pi


namespace Matrix

variable {α β κ ι γ M : Type*} (A : Matrix α β γ) (B : Matrix κ ι γ)

instance [Mul γ] : OuterProduct (Matrix α β γ) (Matrix κ ι γ) (Matrix (α × κ) (β × ι) γ) where
  tprod := Matrix.kronecker

@[simp]
theorem kronecker_apply' [Mul γ] : A ⨂ B = Matrix.kronecker A B := rfl

-- The rest of lemmas are already proven for `Matrix.kronecker`.

open Kronecker

variable [CommRing γ] [StarRing γ]
/- Generalization of statement from @timeroot's repo -/
@[simp]
theorem star_kron (a : Matrix α α γ) (b : Matrix β β γ) : star (a ⊗ₖ b) = (star a) ⊗ₖ (star b) := by
  ext
  simp

namespace UnitaryGroup

variable [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  (A : unitaryGroup α γ) (B : unitaryGroup β γ)

theorem kron_unitary :
    ↑A ⊗ₖ ↑B ∈ unitaryGroup (α × β) γ := by
  simp [Matrix.mem_unitaryGroup_iff]

instance : OuterProduct (unitaryGroup α γ) (unitaryGroup β γ) (unitaryGroup (α × β) γ) where
  tprod a b := ⟨_, kron_unitary a b⟩

@[simp]
theorem kronecker_apply : A ⨂ B = ⟨_, kron_unitary A B⟩ := rfl

@[simp, norm_cast]
theorem coe_unitary_kron (a : unitaryGroup α γ) (b : unitaryGroup β γ) :
  (↑(a ⨂ b) : Matrix (α × β) (α × β) γ)  = ↑a ⊗ₖ ↑b := by rfl

theorem unitary_row_inner {α : Type*} [CommRing α] [StarRing α]
    {n : Type*} [Fintype n] [DecidableEq n] (A : unitaryGroup n α) (i j : n) :
    ∑ k, A i k * star (A j k) = if i = j then 1 else 0 := by
  simpa only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using
    congr_fun₂ (show ↑A * star ↑A = (1 : Matrix n n α) by simp) i j

@[simp]
theorem unitary_kron_mul (a a' : unitaryGroup α γ) (b b' : unitaryGroup β γ) :
    (a ⨂ b) * (a' ⨂ b')  = (a * a') ⨂ (b * b') := by
  ext
  push_cast
  simp only [mul_kronecker_mul]

@[simp]
theorem unitary_kron_one : (1 : unitaryGroup α γ) ⨂ (1 : unitaryGroup β γ) = 1 := by
  simp

@[simp]
theorem unitary_kron_inv (a : unitaryGroup α γ) (b : unitaryGroup β γ) :
  (a ⨂ b)⁻¹ = (a⁻¹ ⨂ b⁻¹) := inv_eq_of_mul_eq_one_left (by simp)

@[simps]
def rTensorHom : (unitaryGroup α γ) →* unitaryGroup (α × β) γ where
  toFun U := U ⨂ (1 : unitaryGroup β γ)
  map_one' := by simp
  map_mul' := by simp

@[simps]
def lTensorHom : (unitaryGroup β γ) →* unitaryGroup (α × β) γ where
  toFun U := (1 : unitaryGroup α γ) ⨂ U
  map_one' := by simp
  map_mul' := by simp

end UnitaryGroup

end Matrix


namespace Unitary.EuclideanCLM

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
variable {𝕜 : Type*} [RCLike 𝕜]
variable
  (A A' : unitary ((EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)))
  (B B' : unitary ((EuclideanSpace 𝕜 m) →L[𝕜] (EuclideanSpace 𝕜 m)))

noncomputable instance :
    OuterProduct
      (unitary ((EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)))
      (unitary ((EuclideanSpace 𝕜 m) →L[𝕜] (EuclideanSpace 𝕜 m)))
      (unitary ((EuclideanSpace 𝕜 (n × m)) →L[𝕜] (EuclideanSpace 𝕜 (n × m)))) where
  tprod A B := unitaryGroupEquiv (unitaryGroupEquiv.symm A ⨂ unitaryGroupEquiv.symm B)

theorem tensorProduct_def :
  (A ⨂ B) = unitaryGroupEquiv (unitaryGroupEquiv.symm A ⨂ unitaryGroupEquiv.symm B) := rfl

@[simp]
theorem tensorProduct_apply (v : EuclideanSpace 𝕜 (n × m)) :
    (A ⨂ B) v =
      (((unitaryGroupEquiv.symm A) ⨂ (unitaryGroupEquiv.symm B))
        : Matrix (n × m) (n × m) 𝕜).mulVec v := by
  simp [tensorProduct_def]

@[simp]
theorem tensorProduct_mul :
    (A ⨂ B) * (A' ⨂ B') = (A * A') ⨂ (B * B') := by
  ext
  simp

@[simp]
theorem tensorProduct_one :
  (1 : unitary ((EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)))
    ⨂ (1 : unitary ((EuclideanSpace 𝕜 m) →L[𝕜] (EuclideanSpace 𝕜 m))) = 1 := by
  ext
  simp

@[simp]
theorem inv_tensorProduct :
  (A ⨂ B)⁻¹ = (A⁻¹ ⨂ B⁻¹) := inv_eq_of_mul_eq_one_left (by simp)

end Unitary.EuclideanCLM
