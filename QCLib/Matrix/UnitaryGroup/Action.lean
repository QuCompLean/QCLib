/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.PiKronecker
public import QCLib.Matrix.Action

/-!
# Some actions of the `unitaryGroup`

## To do

Rethink what is necessary.  Write docstrings.
-/

@[expose] public section

open Matrix

variable {n : Type} [Fintype n] [DecidableEq n]
variable {α : Type*} [CommRing α] [StarRing α]

/-
## Interaction between `unitary α` and `unitaryGroup n α`
-/

-- Shortcut instance. Otherwise, instance search times out otherwise if Mathlib is imported.
instance (priority := 1100) instUnitarySMulShortcut : SMul (unitaryGroup n α) (unitaryGroup n α) :=
    instSMulOfMul

/-- Provides `(z • U) • V = z • (U • V)` which implies `(z • U) * V = z • (U * V)` -/
instance : IsScalarTower (unitary α) (unitaryGroup n α) (unitaryGroup n α) :=
  ⟨fun z U V => by ext; simp⟩

instance : IsScalarTower (unitary α) (unitaryGroup n α) (n → α) :=
  ⟨fun z U v => by ext; simp only [Submonoid.smul_def, Unitary.coe_smul, smul_assoc]⟩

/-- Provides `z • (U • V) = U • (z • V)` which implies `z • (U * V) = U * (z • V)` -/
instance : SMulCommClass (unitary α) (unitaryGroup n α) (unitaryGroup n α) :=
  ⟨fun z U V => by ext; simp⟩

instance : SMulCommClass (unitary α) (unitaryGroup n α) (n → α) :=
  ⟨fun z U v => by ext; simp only [Submonoid.smul_def]; rw [smul_comm]⟩

instance [Inhabited n] : FaithfulSMul (unitary α) (unitaryGroup n α) where
  eq_of_smul_eq_smul h := by
    simpa [Submonoid.smul_def] using congrArg (fun V ↦ V default default) (h 1)

/-
## Action on vectors
-/

@[simp]
theorem Matrix.unitaryGroup.smul_def {α m : Type*}
    [Fintype m] [DecidableEq m] [CommRing α] [StarRing α]
    (U : unitaryGroup m α) (B : Matrix m l α) : U • B = (↑U : Matrix m m α) * B := by
  with_reducible_and_instances rfl

-- dooesn't use previous instandce
theorem Matrix.unitaryGroup.smul_vec_def
    {α m : Type*} [Fintype m] [DecidableEq m] [CommRing α] [StarRing α]
    (U : unitaryGroup m α) (v : m → α) : U • v = ↑U *ᵥ v := by
  simp [Submonoid.smul_def]

/-
## Misc
-/

/-- Collect scalars on the left -/
@[simp]
theorem smul_assoc_symm {α M N : Type*} [SMul M N] [SMul N α] [SMul M α] [IsScalarTower M N α]
  (x : M) (y : N) (z : α) : x • y • z = (x • y) • z := (IsScalarTower.smul_assoc x y z).symm

-- Is there a `FreeAction` type class? Should there by?
theorem unitary_smul_free [Inhabited n] (s : unitary α) (U : unitaryGroup n α) :
    s • U = U ↔ s = 1 := .intro
      (fun h ↦ by simpa [Submonoid.smul_def] using congrArg (fun V ↦ (V * U⁻¹) default default) h)
      (fun h ↦ by simp [h])

example (U V : unitaryGroup n α) (z : unitary α) :
    U * (z • V) = z • (U * V) := mul_smul_comm z U V

@[simp]
lemma unitary_smul_mul_nf (U V : unitaryGroup n α) (z : unitary α) :
    (z • U) * V = z • (U * V) := smul_mul_assoc z U V


section OuterProduct

variable {ι : Type*} [Fintype ι] {l m n : ι → Type*} {R : Type*}
variable [DecidableEq ι] [∀ i, DecidableEq (n i)] [∀ i, Fintype (n i)] [CommRing R] [StarRing R]

open scoped OuterProduct

@[simp]
theorem piKroneckerUnitary_smul_vec (U : Π i, unitaryGroup (n i) R) (v : Π i, n i → R) :
    (⨂ i, U i) • (⨂ i, v i) = (⨂ i, (U i) • (v i)) := by
  simp [Matrix.unitaryGroup.smul_vec_def]

end OuterProduct


end
