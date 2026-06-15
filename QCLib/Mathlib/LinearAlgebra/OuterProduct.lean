module

public import Mathlib


public section

/- ! Note : `Matrix.vecMulVec` exists but it produces matrices, not tuples.
  It is possible to convert the output of `vecMulVec` to a tuple by tranpsorting
  it along `Matrix.of.symm` equiv, however, at the moment the benefit of doing so
  is not clear.

  TBD : Decide between cartasian product and currying.
  For now, cartasian product is avoided because it requires writing more
  `(r ⊗ s) ⟨i, j⟩` vs `(r ⊗ s) i j`. Furthermore `fin_cases` can be called on
  `i` or `j` directly wheras it cannot be used for `a.1` or `a.2` with
  `a = ⟨i, j⟩ ` without generalizing `a.1` and `a.2`.
-/

variable {α β γ M : Type*} (f : γ → γ → γ) (r : α → γ) (s : β → γ)

def OuterProductMap : α → β → γ :=
  fun (i j) ↦ f (r i) (s j)

@[simp]
theorem OuterProductMap_apply (i j) :
  OuterProductMap f r s i j = f (r i) (s j) := by rfl

def OuterProduct [Mul γ] := OuterProductMap (· * ·) r s

infixl:100 " ⊗ " => OuterProduct

@[simp]
theorem outerProduct_apply [Mul γ] (i j) : (r ⊗ s) i j = r i * s j := by rfl

@[simp]
theorem zero_outerProduct [MulZeroClass γ] : (0 : α → γ) ⊗ s = 0 := by
  ext
  simp

@[simp]
theorem outerProduct_zero [MulZeroClass γ] : r ⊗ (0 : β → γ) = 0 := by
  ext
  simp

@[simp]
theorem add_outerProduct [Mul γ] [Add γ] [RightDistribClass γ] (r s : α → γ) (w : β → γ) :
    (r + s) ⊗ w = (r ⊗ w) + s ⊗ w := by
  ext
  simp [add_mul]

@[simp]
theorem outerProduct_add [Mul γ] [Add γ] [LeftDistribClass γ] (r s : α → γ) (w : β → γ) :
    w ⊗ (r + s) = (w ⊗ r) + w ⊗ s := by
  ext
  simp [mul_add]

@[simp]
theorem smul_outerProduct [Mul γ] [SMul M γ] [IsScalarTower M γ γ] (c : M) :
    (c • r) ⊗ s = c • (r ⊗ s) := by
  ext
  simp [smul_mul_assoc]

@[simp]
theorem outerProduct_smul [Mul γ] [SMul M γ] [SMulCommClass M γ γ] (c : M) :
    r ⊗ (c • s) = c • (r ⊗ s) := by
  ext
  simp [mul_smul_comm]

@[simp]
theorem outerProduct_smul_smul [Mul γ] [Monoid M] [MulAction M γ]
    [IsScalarTower M γ γ] [SMulCommClass M γ γ] (c d : M) :
    (c • r) ⊗ (d • s) = (d * c) • (r ⊗ s) := by
  rw [outerProduct_smul, smul_outerProduct, smul_smul]

@[simp]
theorem neg_outerProduct [Mul γ] [HasDistribNeg γ] :
    (-r) ⊗ s = -(r ⊗ s) := by
  ext
  simp [neg_mul]

@[simp]
theorem outerProduct_neg [Mul γ] [HasDistribNeg γ] :
    r ⊗ (-s) = -(r ⊗ s) := by
  ext
  simp [mul_neg]

def outerProductLinearMap [CommSemiring γ] : (α → γ) →ₗ[γ] (β → γ) →ₗ[γ] (α → β → γ) :=
  LinearMap.mk₂ γ (· ⊗ ·) (by simp) (by simp) (by simp) (by simp)
