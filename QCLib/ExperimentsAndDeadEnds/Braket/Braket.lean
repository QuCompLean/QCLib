/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Gross
-/

/-

# Dirac notation

Dirac notation for matrices. See "BraketL.lean" docstring for more information.

-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Unique
public import Qml.Tactic -- Split Tactic to registerSimp and import that instead?

public section

open scoped Matrix

variable {ι : Type*} [Fintype ι]


notation "⟪" x ", " y "⟫" => dotProduct (star x) y

-- TBD: This uses `notation3`. Presumably, one should use more modern constructions.
-- This seem to require writing a `delaborator`.
scoped[Braket] notation3 " ∣" ψ:90 "⟩⟨" φ:90 "∣ " => Matrix.vecMulVec ψ (star φ)
scoped[Braket] notation3:max " ⟨" φ:90 "∣" => (Matrix.vecMulVec ![(1 : ℂ)] (star φ))
scoped[Braket] notation3:max "∣" ψ:90 "⟩ " => Matrix.vecMulVec ψ (star ![(1 : ℂ)])
-- TBD: Treat 1x1 case.

-- Makes `vecMulVec` behave more like the `rankOne` API
attribute [-simp] Matrix.vecMulVec_cons
attribute [-simp] Matrix.cons_vecMulVec
attribute [simp] Matrix.vecMulVec_mul_vecMulVec
attribute [simp] Matrix.vecMulVec_apply

section Braket

namespace Braket

variable {ι : Type*} (ψ φ : ι → ℂ)

@[simp]
theorem star_scalar_one : star ![(1 : ℂ)] = ![1] := by ext; simp

@[simp]
theorem ket_plus_ket : ∣ψ⟩ + ∣φ⟩ = ∣(ψ + φ)⟩ := by ext; simp

@[simp]
theorem ket_adjoint_eq_bra : ∣ψ⟩ᴴ = ⟨ψ∣ := by simp

@[simp]
theorem ket_bra_adjoint_eq : (∣ψ⟩⟨φ∣)ᴴ  = ∣φ⟩⟨ψ∣ := by simp

@[simp]
theorem bra_adjoint_eq_ket : (⟨ψ∣)ᴴ = ∣ψ⟩ := by simp

variable [Fintype ι]

@[simp]
theorem ketbraketbra_eq {κ γ : Type*} (α : κ → ℂ) (β : γ → ℂ) :
    ∣α⟩⟨ψ∣ * ∣φ⟩⟨β∣ = ⟪ψ, φ⟫ • ∣α⟩⟨β∣ := by simp

@[simp]
theorem vecMulVec_unique_unique (x z : ℂ) : Matrix.vecMulVec ![x] ![z] = !![x * z] := by ext; simp

@[simp]
theorem braket_eq : ⟨ψ∣ * ∣φ⟩ =  ⟪ψ, φ⟫ • !![1] := by simp

@[simp]
theorem ketbraket_eq_smul_ket (χ : ι → ℂ) : ∣χ⟩ * ⟨ψ∣ * ∣φ⟩ = ⟪ψ, φ⟫ • ∣χ⟩ := by
  ext; simp; ring

end Braket

-- !! Norm on the spaces we work with is sup norm!
#synth NormedSpace ℂ ((Fin 2) → ℂ)

-- -- TBD: Prove that this is an isometry for the dot product?
-- noncomputable abbrev toEuclidean := (EuclideanSpace.equiv ι ℂ).symm


/-!

# Standard basis

-/

noncomputable def BasisVector {ι : Type*} [Finite ι] (i : ι) : (ι → ℂ) :=
  Pi.basisFun ℂ ι i

@[matrixExpand]
theorem basisVector_def (ι : Type*) [Finite ι] (i : ι) :
  BasisVector i = Pi.basisFun ℂ ι i := by rfl

/-- The computational basis. -/
notation3:max "δ[" i:90 "] " =>
  BasisVector i

/-
## Notation
-/

open scoped Braket

scoped[Braket] notation3:max "‖" i:90 "⟩ " =>
  Matrix.vecMulVec (BasisVector i) (star ![(1 : ℂ)])

/- Tests -/
#check ‖(0 : Fin 2)⟩
#check fun (n : ℕ) (k : Fin n → Fin 2) ↦ ‖k⟩

end Braket

/-
# Singleton indices

We have defined `∣φ⟩` as a matrix with right index type `Fin 1`. Any other
singleton type gives rise to an equivalent definition. That's relevant, because
the `PiKroneckerProduct` of such matrices has right index type `ι → Fin 1` -- a
different singleton type.

Here, we set up some machinery TBD.

However, having played around with these defs a bit, my recommendation is to
avoid havint to use them.
-/

section Singleton

open Matrix

namespace Matrix

variable {n m α : Type*}

/-
### Coercion of 1-1 matrices to scalars
-/

@[coe]
abbrev toScalar [Unique n] [Unique m] : Matrix n m α → α :=
  uniqueEquiv.toFun

-- Set priority higher than the instance below, which triggers for just one `Unique`
/-- Coerce 1x1 matrices to scalars -/
instance (priority := high) [Unique n] [Unique m] : CoeOut (Matrix n m α) α := ⟨toScalar⟩

section Tests

open Braket
variable {ι : Type*} [Fintype ι] (ψ φ : ι → ℂ)

#check (!![1] : ℕ) -- `↑!![1] : ℕ`

@[simp]
theorem coe_braket : (⟨ψ∣ * ∣φ⟩ : ℂ) = ⟪ψ, φ⟫ := by simp

end Tests

/-
### Unique right index
-/

@[ext]
theorem uniqueRight_eq_iff [Unique m] (A B : Matrix n m α) :
    (∀ i,  A i default = B i default) → A = B := fun h ↦ by
  ext i j
  exact (Subsingleton.elim j default) ▸ (h i)

@[coe]
abbrev reindexUniqueRight {m' : Type*} [Unique m] [Unique m'] [Semiring α] :
    Matrix n m α → Matrix n m' α :=
  reindexLinearEquiv α α (Equiv.refl n) (Equiv.ofUnique _ _)

instance [Unique m] [Semiring α] : CoeOut (Matrix n m α) (Matrix n (Fin 1) α) :=
  ⟨reindexUniqueRight⟩

@[simp, norm_cast]
theorem ofUniqueRight_apply {m' : Type*} [Unique m] [Unique m'] [Semiring α]
    (M : Matrix n m α) (i : n) (j : m') : (reindexUniqueRight M) i j = M i default := by
  rfl

/-- A reindex on the right commutes with left-multiplication -/
theorem reindex_right_comm_left_mul {l m n o α : Type*} [Fintype m] [CommSemiring α]
    (A : Matrix l m α) (B : Matrix m n α) (e : n ≃ o) :
    (A * (reindex (Equiv.refl m) e B)) = reindex (Equiv.refl l) e (A * B) := by
  ext
  simp [mul_apply]

end Singleton.Matrix
