/-
Copyright (c) 2026 Davood Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import QCLib.Mathlib.LinearAlgebra.PiOuterProduct
public import QCLib.LinearAlgebra.UnitaryGroup.Basic

import QCLib.Tactic.MatrixExpand
import QCLib.Mathlib.Lemmas

/-!
# Bases

## Main definitions

* `BasisVector`, a synonym for `Pi.basisFun ℂ`
* `Qubit` for `Fin 2`, so that the vector space for a single qubit is `Qubit → ℂ`
* `Register n` for `(Fin n) → Qubit`, so that the vector space for `n` qubits is `Register n → ℂ`
* `PiOuterPrdocutInst` A type class instance that provides outer product notation
  for dependent families of `EuclideanSpace` vectors.

## Main results

* `basisVector_eq_prod` standard basis functions factorize
* `PiOuterProduct.toMultilinearMap` Outer products as multilinear maps.

This file also collects `•` application

## Notation

* `δ[i]` for `BasisVector i`

-/

-- creates a simp loop with `WithLp.zero_def`
attribute [-simp] WithLp.toLp_zero

-- why aren't these set?
attribute [coe] WithLp.ofLp
attribute [norm_cast] WithLp.ofLp_smul

public section

/-
Missing instance, which should go into the section around `WithLp.instNontrivial`.
-/
section WithLpMissingInstances

namespace WithLp

open scoped ENNReal

variable (p : ℝ≥0∞) (K K' : Type*) {K'' : Type*} (V : Type*) {V' V'' : Type*}

@[to_additive (attr := simps)]
instance instOne [One V] : One (WithLp p V) := (WithLp.equiv p V).one

end WithLpMissingInstances.WithLp

open EuclideanSpace PiOuterProduct Function

variable {ι : Type*} [Fintype ι]

namespace EuclideanSpace

variable {α : Type*} (l : ι → Type*)

@[ext]
theorem ext {α n : Type*} {x y : EuclideanSpace α n} (h : x.ofLp = y.ofLp) : x = y :=
  WithLp.ofLp_injective 2 h

@[simp]
theorem ofLp_update_apply {ι : Type*} [DecidableEq ι] {l : ι → Type*}
    (f : Π i, EuclideanSpace α (l i)) (i' : ι) (x : EuclideanSpace α (l i'))
    (j : Π i, l i) (i : ι) :
    (update f i' x i).ofLp (j i)
      = update (fun i ↦ (f i).ofLp (j i)) i' (x.ofLp (j i')) i :=
  apply_update (fun i (v : EuclideanSpace α (l i)) ↦ v.ofLp (j i)) f i' x i

instance instPiOuterProduct [CommMonoid α] :
    PiOuterProduct (fun i ↦ EuclideanSpace α (l i)) (EuclideanSpace α (Π i, l i)) where
  tprod f := WithLp.toLp 2 (⨂ i, ((f i) : (l i → α)))

@[simp, norm_cast]
theorem ofLp_injective [CommMonoid α] (f : Π i, EuclideanSpace α (l i)) :
    (⨂ i, f i).ofLp = (⨂ i, (f i).ofLp) := rfl

example [CommMonoid α] (f : (i : ι) → EuclideanSpace α (l i)) (j) :
    (⨂ i, f i) j = ∏ i, f i (j i) := by simp

-- remove? geometrically, the all-ones vector isn't distinguished in an l2 space.
@[simp]
theorem piOuterProduct_one [CommMonoid α] : (⨂ i, (1 : EuclideanSpace α (l i))) = 1 := by
  ext1
  simp

@[simp]
theorem piOuterProduct_zero [CommMonoidWithZero α] (f : Π i, EuclideanSpace α (l i))
    (h : ∃ i, f i = 0) : (⨂ i, f i) = 0 := by
  ext j
  obtain ⟨i, hi⟩ := h
  simpa using Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

@[simp]
theorem piOuterProduct_smul [CommSemiring α] [DecidableEq ι]
    (f : Π i, EuclideanSpace α (l i)) (i : ι) (s : α) (x : EuclideanSpace α (l i)) :
    (⨂ j, (update f i (s • x)) j) = s • (⨂ j, (update f i x) j) := by
  ext
  simp [Finset.prod_update_of_mem, mul_assoc]

-- Lean only synthesizes `Add` under `SeminormedAddCommGroup` assumption.
-- See `PiLp.add_apply`. TBD: Investigate.
@[simp]
theorem piOuterProduct_add [DecidableEq ι] [CommMonoid α]
    [SeminormedAddCommGroup α] [RightDistribClass α]
    (f : Π i, EuclideanSpace α (l i)) (i : ι) (x y : EuclideanSpace α (l i)) :
    (⨂ j, (update f i (x + y)) j) = (⨂ j, (update f i x) j) + (⨂ j, (update f i y) j) := by
  ext
  simp [Finset.prod_update_of_mem, add_mul]

@[simps, expose]
def PiOuterProduct.toMultilinearMap [SeminormedCommRing α] :
    MultilinearMap α (fun i ↦ EuclideanSpace α (l i)) (EuclideanSpace α (Π i, l i)) where
  toFun f := ⨂ i, f i
  map_update_add' := by simp
  map_update_smul' := by simp

theorem piOuterProduct_smul_univ [SeminormedCommRing α] (c : ι → α)
    (f : Π i, EuclideanSpace α (l i)) :
    (⨂ i, c i • f i) = (∏ i, c i) • (⨂ i, f i) := by
  ext1
  simp [Pi.piOuterProduct_smul_univ]

theorem piOuterProduct_smul_const [SeminormedCommRing α] (a : α)
    (f : Π i, EuclideanSpace α (l i)) :
    (⨂ i, a • f i) = a ^ (Fintype.card ι) • (⨂ i, f i) := by
  ext1
  simp [Pi.piOuterProduct_smul_const]

theorem piOuterProduct_univ_sum [DecidableEq ι] [SeminormedCommRing α] {κ : Type*} [Fintype κ]
    (g : (i : ι) → κ → EuclideanSpace α (l i)) :
    (⨂ i, ∑ j : κ, g i j) = ∑ k : (ι → κ), ⨂ i, g i (k i) := by
  ext1
  simp [Pi.piOuterProduct_univ_sum]

end EuclideanSpace

noncomputable def BasisVector (i : ι) :=
  basisFun ι ℂ i

@[matrixExpand]
theorem basisVector_def (i : ι) :
  BasisVector i = basisFun ι ℂ i := by rfl

-- TBD: scope
/-- The computational basis. -/
notation3:max "δ[" i:90 "] " => BasisVector i

-- `ext` lemma stated for `SMul` action of unitaries on vectors.
-- TBD: Get rid of this? Formulate in terms of `toLin` and general Bases? State
-- for `MatrixLike` objects?
-- More generally, decide whether to use `•` for actions on vectors
-- Move to other module?
theorem Matrix.UnitaryGroup.ext_col [DecidableEq ι]
    {U V : Matrix.unitaryGroup ι ℂ} :
    (∀ i : ι, (U : Matrix ι ι ℂ).col i = (V : Matrix ι ι ℂ).col i) → U = V := by
  intro h
  apply Subtype.ext
  exact Matrix.ext_col h

variable [DecidableEq ι]

open Matrix in
theorem Matrix.unitaryGroup.EuclideanSpace.smul_def
    {α m : Type*} [Fintype m] [DecidableEq m] [CommRing α] [StarRing α]
    (U : unitaryGroup m α) (v : EuclideanSpace α m) : U • v = WithLp.toLp 2 (↑U *ᵥ v.ofLp) := by
  ext
  simp [Submonoid.smul_def]

open Matrix in
@[simp]
theorem Matrix.unitaryGroup.EuclideanSpace.smul_coe
  {α m : Type*} [Fintype m] [DecidableEq m] [CommRing α] [StarRing α]
    (U : unitaryGroup m α) (v : EuclideanSpace α m) : ((U • v) : m → α) = (↑U *ᵥ v.ofLp) := by
  ext
  simp [Submonoid.smul_def]

theorem Matrix.UnitaryGroup.ext_smul_basis
    {U V : Matrix.unitaryGroup ι ℂ} : (∀ i : ι, (U • δ[i]) = V • δ[i]) → U = V := by
  simpa [basisVector_def, Matrix.unitaryGroup.EuclideanSpace.smul_def] using ext_col

@[simp]
theorem Matrix.UnitaryGroup.diagonal_smul_basisVector
    (d : ι → unitary ℂ) (i : ι) : (diagonalMonoidHom d) • δ[i] = (d i) • δ[i] := by
  ext j
  simp [Submonoid.smul_def, basisVector_def, Pi.single_apply]

@[simp]
theorem Matrix.diagonal_smul_basisVector (d : ι → ℂ) (v : ι) :
    Matrix.diagonal d • δ[v] = d v • δ[v] := by
  ext i
  simp [basisVector_def, basisFun_apply, Pi.single_apply]

theorem Matrix.UnitaryGroup.apply_basis {U : Matrix.unitaryGroup ι ℂ} (v : ι) :
    U • δ[v] = ∑ i, U i v • δ[i] := by
  ext
  simp [basisVector_def, Pi.single_apply, Submonoid.smul_def]

@[simp]
theorem Matrix.UnitaryGroup.piKroneckerUnitary_smul_vec
    (l : ι → Type*) [∀ i, DecidableEq (l i)] [∀ i, Fintype (l i)]
    (U : Π i, unitaryGroup (l i) ℂ)
    (v : (i : ι) → EuclideanSpace ℂ (l i)) :
    (⨂ i, U i) • (⨂ i, v i) = (⨂ i, (U i) • (v i)) := by
  ext1
  simp

section SMul

section Qubits

abbrev Qubit := Fin 2
abbrev Register (n : Nat) := (Fin n) → Qubit

open Complex Matrix
open scoped PiOuterProduct

theorem basisVector_eq_prod {d} {n : ℕ} (k : Fin n → Fin d) : δ[k] = ⨂ i, δ[(k i)] := by
  ext
  simp [basisVector_def, ← Pi.single_eq_prod, ← Pi.single_apply]

end Qubits
