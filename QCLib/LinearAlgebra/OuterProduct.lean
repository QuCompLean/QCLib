module


public import QCLib.Circuit.Embed

public section

/-
Note: `Matrix.vecMulVec` already provides an outer product operation, but its
result is a matrix rather than a tuple-indexed function.

One could transport the result along `Matrix.of.symm` to obtain a tuple-indexed
representation. At present, however, it is unclear whether this would provide
any practical advantage.

There is also a design choice between representing tensor indices as a Cartesian
product or as a curried function.

Using a Cartesian product requires expressions such as

* `(r ⊗ s) ⟨i, j⟩`

instead of

* `(r ⊗ s) i j`.

The curried representation is often more convenient for proofs. For example,
`fin_cases` can be applied directly to `i` or `j`, whereas with a pair
`a : α × β` one typically has to first generalize `a.1` and `a.2`.

On the other hand, equivalences such as `Equiv.piSplitAt` naturally produce
Cartesian-product representations, which makes them easier to use in that
setting.
-/

variable {α β γ M : Type*} (f : γ → γ → γ) (r : α → γ) (s : β → γ)

def OuterProductMap : α × β → γ :=
  fun ⟨i, j⟩ ↦ f (r i) (s j)

@[simp]
theorem OuterProductMap_apply (i : α) (j : β) :
    OuterProductMap f r s (i, j) = f (r i) (s j) := by rfl

def OuterProduct [Mul γ] : α × β → γ := OuterProductMap (· * ·) r s

infixl:100 " ⊗ " => OuterProduct

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

def outerProductLinearMap [CommSemiring γ] :
    (α → γ) →ₗ[γ] (β → γ) →ₗ[γ] (α × β → γ) :=
  LinearMap.mk₂ γ (· ⊗ ·) (by simp) (by simp) (by simp) (by simp)

open Matrix.UnitaryGroup Equiv Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {k : ι → Type u_2}
  [(i : ι) → DecidableEq (k i)] [(i : ι) → Fintype (k i)]

theorem single_apply_basis' (v : Π i, k i) (i : ι) (U : 𝐔[k i]) :
    single' i U • δ[v] = (U • δ[v i]) ⊗ δ[fun a : {j // j ≠ i} => v a] ∘ piSplitAt i _ := by
  ext
  simp [basisVector_def, Submonoid.smul_def, blockDiagonal_apply, Pi.single_apply]

theorem bipartite_apply_basis' (i j : ι) (U : 𝐔[k i × k j]) (h : i ≠ j) (v : Π i, k i) :
    bipartite' i j U h • δ[v] =
      ((U • δ[(v i, v j)]) ⊗ δ[fun a : {m // m ≠ i ∧ m ≠ j} => v a]) ∘ (piSplitAtPair i j) := by
  ext
  simp [basisVector_def, Submonoid.smul_def, blockDiagonal_apply, funext_iff, Pi.single_apply]
