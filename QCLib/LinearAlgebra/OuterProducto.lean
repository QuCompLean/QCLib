/-
Copyright (c) 2026 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module


public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Pi

public section

/-
# Binary tensor product of concrete vectors

Experimental file.

## Implementation notes

`Matrix.vecMulVec` already provides an outer product operation, but its
result is a matrix rather than a tuple-indexed function.
-/

variable {α β γ M : Type*} (f : γ → γ → γ) (r : α → γ) (s : β → γ)

def OuterProductMap : α × β → γ :=
  fun ⟨i, j⟩ ↦ f (r i) (s j)

@[simp]
theorem OuterProductMap_apply (i : α) (j : β) :
    OuterProductMap f r s (i, j) = f (r i) (s j) := by rfl

def OuterProduct [Mul γ] : α × β → γ := OuterProductMap (· * ·) r s

scoped[OuterProduct] infixl:100 " ⊗ " => OuterProduct

open OuterProduct

@[simp]
theorem outerProduct_apply [Mul γ] (i : α) (j : β) :
    (r ⊗ s) (i, j) = r i * s j := by rfl

@[simp]
theorem zero_outerProduct [MulZeroClass γ] : (0 : α → γ) ⊗ s = 0 := by
  ext ⟨i, j⟩; simp

@[simp]
theorem outerProduct_zero [MulZeroClass γ] : r ⊗ (0 : β → γ) = 0 := by
  ext ⟨i, j⟩; simp

@[simp]
theorem add_outerProduct [Mul γ] [Add γ] [RightDistribClass γ] (r s : α → γ) (w : β → γ) :
    (r + s) ⊗ w = (r ⊗ w) + s ⊗ w := by
  ext ⟨i, j⟩; simp [add_mul]

@[simp]
theorem outerProduct_add [Mul γ] [Add γ] [LeftDistribClass γ] (r s : α → γ) (w : β → γ) :
    w ⊗ (r + s) = (w ⊗ r) + w ⊗ s := by
  ext ⟨i, j⟩; simp [mul_add]

-- Weaken assumptions on `γ`?
theorem sum_outerProduct [CommRing γ] (w : β → γ)
    {ι : Type*} (S : Finset ι) (f : ι → (α → γ)) :
    (∑ i ∈ S, f i) ⊗ w = ∑ i ∈ S, f i ⊗ w := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => simp_all

theorem outerProduct_sum [CommRing γ] (r : α → γ)
    {ι : Type*} (S : Finset ι) (f : ι → (β → γ)) :
    r ⊗ (∑ i ∈ S, f i) = ∑ i ∈ S, r ⊗ f i := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih => simp_all

@[simp]
theorem smul_outerProduct [Mul γ] [SMul M γ] [IsScalarTower M γ γ] (c : M) :
    (c • r) ⊗ s = c • (r ⊗ s) := by
  ext ⟨i, j⟩; simp [smul_mul_assoc]

@[simp]
theorem outerProduct_smul [Mul γ] [SMul M γ] [SMulCommClass M γ γ] (c : M) :
    r ⊗ (c • s) = c • (r ⊗ s) := by
  ext ⟨i, j⟩; simp [mul_smul_comm]

@[simp]
theorem outerProduct_smul_smul [Mul γ] [Monoid M] [MulAction M γ]
    [IsScalarTower M γ γ] [SMulCommClass M γ γ] (c d : M) :
    (c • r) ⊗ (d • s) = (d * c) • (r ⊗ s) := by
  rw [outerProduct_smul, smul_outerProduct, smul_smul]

@[simp]
theorem neg_outerProduct [Mul γ] [HasDistribNeg γ] :
    (-r) ⊗ s = -(r ⊗ s) := by
  ext ⟨i, j⟩; simp [neg_mul]

@[simp]
theorem outerProduct_neg [Mul γ] [HasDistribNeg γ] :
    r ⊗ (-s) = -(r ⊗ s) := by
  ext ⟨i, j⟩; simp [mul_neg]

theorem outerProduct_left_injective
    [MulZeroClass γ] [IsRightCancelMulZero γ] (hs : s ≠ 0) :
    Function.Injective (fun r : α → γ => r ⊗ s) := by
  intro r r' h
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hs
  ext i
  have h' := congrArg (fun f => f (i, j)) h
  simp_all

theorem outerProduct_right_injective
    [MulZeroClass γ] [IsLeftCancelMulZero γ] (hr : r ≠ 0) :
    Function.Injective (fun s : β → γ => r ⊗ s) := by
  intro s s' h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hr
  ext j
  have h' := congrArg (fun f => f (i, j)) h
  simp_all

def outerProductBilinearMap [CommSemiring γ] :
    (α → γ) →ₗ[γ] (β → γ) →ₗ[γ] (α × β → γ) :=
  LinearMap.mk₂ γ (· ⊗ ·) (by simp) (by simp) (by simp) (by simp)
