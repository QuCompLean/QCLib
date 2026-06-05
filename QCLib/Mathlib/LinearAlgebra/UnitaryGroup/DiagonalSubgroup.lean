/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Data.Matrix.Action
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Diagonal unitary matrices

This file defines the diagonal subgroup of the unitary group.

## Implementation Notes

There are two natural models of that group, namely:
* `unitary (n → R)`
* `n → unitary R`

The first option seems nicer mathematically. But it's easier to define elements
of the second one. We develop both for now, but one should probably focus on one.
We'll put defs pertaining to these two points of view into the namespaces
`Unitary.Pi` and `Pi.Unitary` respectively.

## Main definitions

* `Matrix.UnitaryGroup.diagonalSubgroup`
* `Pi.Unitary.diagonalMulEquiv : unitary (n → R) ≃* diagonalSubgroup n R`
* `Unitary.Pi.diagonalMulEquiv : (n → unitary R) ≃* diagonalSubgroup n R`

## To do

With the benefit of hindsight, should probably go for the 2nd model.
-/

@[expose] public section

section Lemmas

-- Rewrites the membership condition for `unitary` in a way that's compatible
-- with the one of `unitaryGroup`.
@[to_additive]
theorem mul_and_mul_iff_mul {M} [MulOne M] [IsDedekindFiniteMonoid M] {a b : M} :
    a * b = 1 ∧ b * a = 1 ↔ b * a = 1 := ⟨And.right, fun h ↦ ⟨mul_eq_one_comm.mpr h, h⟩⟩

@[simp]
theorem star_diagonal {ι α : Type*} [NonUnitalNonAssocSemiring α] [DecidableEq ι] [StarRing α]
    (f : ι → α) : star (Matrix.diagonal f) = Matrix.diagonal (star f) := by
  ext i j
  by_cases h : i = j
  · simp [h]
  · have : i ≠ j := by grind
    simp [this, this.symm]

end Lemmas

section Unitary.Pi

-- We assume `[CommRing R]` to avoid having to treat left and right inverses separetely.
-- TBD: Generalize?
variable {R : Type*} [CommRing R] [StarRing R]
variable {n : Type*}

instance : CoeFun (unitary (n → R)) fun _ ↦ n → R where coe A := A.val

/-- A function is unitary iff it takes values in the unitary scalars -/
theorem Unitary.Pi.mem_unitary (d : n → R) : (d ∈ unitary (n → R)) ↔ ∀ i, d i ∈ unitary R := by
  simp only [Unitary.mem_iff, mul_and_mul_iff_mul]
  exact ⟨fun h i ↦ congrArg (fun d ↦ d i) h, fun h ↦ by ext; simp [h]⟩

/-- Star monoid equivalence between unitary-valued functions and unitary functions -/
@[simps]
def Unitary.Pi.unitaryStarMulEquiv : (n → unitary R) ≃⋆* (unitary (n → R)) where
  toFun d := ⟨fun i ↦ ↑(d i), (mem_unitary _).mpr fun i ↦ SetLike.coe_mem (d i)⟩
  invFun d := fun i ↦ ⟨d i, (mem_unitary ⇑d).mp (SetLike.coe_mem d) i⟩
  map_mul' x y := by with_reducible_and_instances rfl
  map_star' x := by with_reducible_and_instances rfl

end Unitary.Pi

section UnitaryGroup

open Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]

-- Put elsewhere?
/-- Matrix.diagonal as star algebra homomorphism -/
@[simps!]
def Matrix.diagonalStarAlgHom (R : Type*) [CommSemiring R] [StarRing R] :
    (n → R) →⋆ₐ[R] (Matrix n n R) where
      toAlgHom := diagonalAlgHom R
      map_star' d := by simp

variable {R : Type*} [CommRing R] [StarRing R]

/-
Define the diagonal subgroup of the `unitaryGroup` as the image of `unitary (n → R)`
-/
namespace Unitary.Pi

@[simps!]
def diagonal : unitary (n → R) →⋆* unitaryGroup n R :=
  Unitary.map (StarMonoidHom.ofClass (diagonalStarAlgHom R))

theorem diagonal_injective :
    Function.Injective (diagonal : unitary (n → R) →⋆* unitaryGroup n R) :=
  Unitary.map_injective Matrix.diagonal_injective

variable (n R) in
def _root_.Matrix.UnitaryGroup.diagonalSubgroup : Subgroup (unitaryGroup n R) :=
  Subgroup.map diagonal.toMonoidHom ⊤

open Matrix.UnitaryGroup

theorem mem_diagonalSubgroup {U : unitaryGroup n R} :
    (U ∈ diagonalSubgroup n R) ↔ ∃ d : unitary (n → R), diagonal d = U := by
  simp [diagonalSubgroup]

def diagonalSubgroup_ofDiagonal {U : unitaryGroup n R} (h : ∃ d : unitary (n → R), diagonal d = U) :
    diagonalSubgroup n R := ⟨U, mem_diagonalSubgroup.mpr h⟩

open Subgroup in
@[simps!]
noncomputable def diagonalMulEquiv : unitary (n → R) ≃* diagonalSubgroup n R :=
    topEquiv.symm.trans <| equivMapOfInjective ⊤ diagonal.toMonoidHom diagonal_injective

attribute [norm_cast] diagonalMulEquiv_apply_coe_coe

example (d : unitary (n → R)) :
    ((diagonalMulEquiv d) : Matrix n n R) = Matrix.diagonal (d : n → R) := by simp

instance : CommGroup (diagonalSubgroup n R) where
  mul_comm x y :=
    diagonalMulEquiv.symm.injective <| by simp_rw [diagonalMulEquiv.symm.map_mul, mul_comm]

/-- Allows reading indices `M i j`. -/
instance coeFun : CoeFun (diagonalSubgroup n R) fun _ => n → n → R where
  coe A := ↑(A : unitaryGroup n R)

example (x y : diagonalSubgroup n R) : Commute x y := Commute.all x y

/-- Shortcut instance -/
instance : MulAction ↥(unitaryGroup n R) ↥(unitaryGroup n R) :=
    Monoid.toMulAction ↥(unitaryGroup n R)
--
/-- Shortcut instance -/
instance : SMul (diagonalSubgroup n R) (unitaryGroup n R) := Subgroup.instMulAction.toSMul
--
/-- Shortcut instance -/
instance : SMul (diagonalSubgroup n R) (n → R) := DistribMulAction.toDistribSMul.toSMul

instance : SMul (unitary R) (diagonalSubgroup n R) where
  smul a b := ⟨a • b.val, by
    apply mem_diagonalSubgroup.mpr
    have ⟨d, hd⟩ := mem_diagonalSubgroup.mp b.prop
    use a • d
    ext
    simp [← hd]
  ⟩


-- -- TBD: Investigate. Times out w/out shortcuts when Mathlib is imported.
-- -- set_option synthInstance.maxHeartbeats 100000
-- #synth SMul (diagonalSubgroup n R) (unitaryGroup n R)
-- -- set_option synthInstance.maxHeartbeats 100000 in
-- #synth SMul (diagonalSubgroup n R) (n → R)

/-- Provides `(A • B) • z = A • B • z`. -/
instance : IsScalarTower (diagonalSubgroup n R) (diagonalSubgroup n R) (n → R) where
  smul_assoc A B z := by simp [Subgroup.smul_def,Submonoid.smul_def ]

/-- Provides `(A • B) • z = (B • A) • z`. -/
instance : SMulCommClass (diagonalSubgroup n R) (diagonalSubgroup n R) (n → R) where
  smul_comm A B c := by simp_rw [←smul_assoc, smul_eq_mul, mul_comm]

end Unitary.Pi

/- Now re-do, but starting with `n → (unitary R)` -/
namespace Pi.Unitary

@[simps!]
def diagonal : (n → (unitary R)) →⋆* unitaryGroup n R :=
  Unitary.Pi.diagonal.comp Unitary.Pi.unitaryStarMulEquiv.toStarMonoidHom

theorem diagonal_injective : Function.Injective (diagonal (n:=n) (R:=R)) := by
  simp only [diagonal, StarMonoidHom.coe_comp]
  exact Unitary.Pi.diagonal_injective.comp Unitary.Pi.unitaryStarMulEquiv.injective

open Matrix.UnitaryGroup

-- TBD: Clean up

-- TBD: More abstract proof?
theorem mem_diagonalSubgroup {U : unitaryGroup n R} :
    (U ∈ diagonalSubgroup n R) ↔ ∃ d : n → (unitary R), diagonal d = U := by
  simp only [Unitary.Pi.mem_diagonalSubgroup, diagonal]
  exact ⟨fun ⟨d, hd⟩ ↦ ⟨Unitary.Pi.unitaryStarMulEquiv.symm d, by simp_all⟩,
    fun ⟨d, hd⟩ ↦ ⟨Unitary.Pi.unitaryStarMulEquiv d, by simp_all⟩⟩

@[simps]
def diagonalSubgroup_ofDiagonal {U : unitaryGroup n R} (h : ∃ d : (n → unitary R), diagonal d = U) :
    diagonalSubgroup n R := ⟨U, mem_diagonalSubgroup.mpr h⟩

@[simps!]
noncomputable def diagonalMulEquiv : (n → unitary R) ≃* diagonalSubgroup n R :=
  Unitary.Pi.unitaryStarMulEquiv.toMulEquiv.trans Unitary.Pi.diagonalMulEquiv

example (d : n → unitary R) :
    ((diagonalMulEquiv d) : Matrix n n R) = Matrix.diagonal (fun i ↦ ↑(d i)) := by simp

@[simp, norm_cast]
theorem diagonal_coe (d : n → unitary R) :
  ((diagonal d) : Matrix n n R) = Matrix.diagonal fun i ↦ (d i : R) := rfl

@[simp, norm_cast]
theorem diagonalMulEquiv_coe_coe (d : n → unitary R) :
    ((diagonalMulEquiv d) : Matrix n n R) = Matrix.diagonal (fun i ↦ ↑(d i)) := by
  simp [diagonalMulEquiv]

end Pi.Unitary

open Matrix.UnitaryGroup

theorem diagonalSubgroup_pow_apply (D : diagonalSubgroup n R) (k : n) (a : ℕ) :
    (D ^ a) k k = (D k k) ^ a := by
  have ⟨A, ha⟩ := Pi.Unitary.mem_diagonalSubgroup.mp D.prop
  simp [← ha, diagonal_pow]

/-- In practice, this is picked by simp. -/
theorem diagonalSubgroup_coe_pow_apply (D : diagonalSubgroup n R) (k : n) (a : ℕ) :
    ((D : Matrix n n R) ^ a) k k = (D k k) ^ a := by
  have ⟨A, ha⟩ := Pi.Unitary.mem_diagonalSubgroup.mp D.prop
  simp [←ha, diagonal_pow]

end UnitaryGroup

end
