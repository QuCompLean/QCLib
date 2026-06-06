/-
Copyright (c) 2026 David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Algebra.Group.Pi.Units
public import QCLib.Mathlib.LinearAlgebra.PiOuterProduct
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.PiKronecker
public import QCLib.Matrix.UnitaryGroup.DiagonalSubgroup
public import QCLib.Mathlib.Lemmas

/-!

The goal of this file is to treat types that have a canonic injection to matrices
that is compatible with Kronecker products. Examples are unitary / Hermitian /
invertible matrices.

## Main definitions

* `MatrixLike`: class of types with a canonical injection to matrices

* `MatrixLikeOne`: extend `MatrixLike` and adds the field `coe_one`, stating
  that `1` coerces to the identity matrix

* `MatrixLikeMonoid`: extends `MatrixLikeOne` and adds, `coe_mul` stating that
  multiplication in the type commutes with the coercion to matrices.

* `LawfulPiKron`. Class of types that have an operation `kron` such that
  `↑ ∘ kron = PiKroneckerProduct ∘ ↑`, where `↑` represent coercion to matrices.

* `single` tensors supported on a single factor.


## Main results

* `noncommProd_single`: Given a function `f` from an index set `ι` to the `MatrixLikeMonoid` type
  `α`, a product over `single i (f i)`s equals the tensor product of the `f i`.


## Notation

* `⨂ₗ` for `LawfulPiKron` [to be changed to `⨂` if we adopt this approach].


## Implementation notes

* It stands to be decided whether this is overformalized.

* Could add further classes, e.g. for types for which coercion commmutes with taking the inverse.

* Only supports non-dependent tensor products for now. Change?

* Think about whether more result should be marked `simp`.

* Currently, we use `← piKron_matrix_def` quite frequently, to use existing theorems for
  `PiKroneckerProduct`.  If we adopt this approach, these theorems would be
  stated directly for the new definition.

-/

@[expose] public section

/-- Class of types with a canonical injection to matrices. -/
class MatrixLike (A : Type*) (l m : outParam Type*) (R : outParam Type*) where
  coe : A → Matrix l m R
  coe_injective' : Function.Injective coe

attribute [coe] MatrixLike.coe

namespace MatrixLike

section Basic

variable {A : Type*} {l m R : Type*} [i : MatrixLike A l m R]

-- Use low priorities, because presumably, the types will already have coercions
-- to `Matrix` registered.
-- TBD: `SetLike.instCoeTCSet` uses `CoeTC`. Why?
instance (priority := 50) : CoeHead A (Matrix l m R) where coe :=
  MatrixLike.coe

-- Uses the defeq of `Matrix`, but there doesn't seem to be a `CoeFun`?
instance (priority := 50) : CoeFun A (fun _ ↦ l → m → R) where
  coe a := (a : Matrix l m R)

@[simp]
theorem coe_injective : Function.Injective (MatrixLike.coe : A → Matrix l m R) := fun _ _ h =>
  MatrixLike.coe_injective' h

variable {p q : A}

@[simp, norm_cast]
theorem coe_matrix_eq : (p : Matrix l m R) = q ↔ p = q :=
  coe_injective.eq_iff

@[norm_cast] lemma coe_ne_coe : (p : Matrix l m R) ≠ q ↔ p ≠ q := coe_injective.ne_iff

theorem ext' (h : (p : Matrix l m R) = q) : p = q :=
  coe_injective h

theorem ext'_iff : p = q ↔ (p : Matrix l m R) = q :=
  coe_matrix_eq.symm

/-- See comment at `SetLike.ext` -/
theorem ext (h : ∀ i j, p i j = q i j) : p = q :=
  coe_injective <| Matrix.ext h

-- use direction of `SetLike.ext_iff`, which is the opposite of `Matrix.ext_iff`
theorem ext_iff : p = q ↔ ∀ i j, p i j = q i j :=
  coe_injective.eq_iff.symm.trans Matrix.ext_iff.symm

end Basic

section One

/-- Class of types with a canonical injection to matrices, and a compatible `1` element. -/
class _root_.MatrixLikeOne (α : Type*) (l : outParam Type*) (R : outParam Type*)
  [One α] [Zero R] [One R] [DecidableEq l] extends MatrixLike α l l R where
    coe_one : ↑(1 : α) = (1 : Matrix l l R)

variable (α l R : Type*) [One α] [Zero R] [One R] [DecidableEq l] [MatrixLikeOne α l R]

theorem coe_one : ↑(1 : α) = (1 : Matrix l l R) := MatrixLikeOne.coe_one

end One

section Monoid

class _root_.MatrixLikeMonoid (α : Type*) (l : outParam Type*) (R : outParam Type*)
  [Monoid α] [Semiring R] [DecidableEq l] [Fintype l] extends MatrixLikeOne α l R where
    coe_mul : ∀ x y : α, ↑(x * y) = (x : Matrix l l R) * y

variable (α l R : Type*)
variable [Monoid α] [Semiring R] [DecidableEq l] [Fintype l] [MatrixLikeMonoid α l R]

@[norm_cast]
theorem coe_mul : ∀ x y : α, ↑(x * y) = (x : Matrix l l R) * y := MatrixLikeMonoid.coe_mul

/-- Coercion to matrices bundled as a monoid homomorphism -/
@[simps]
def coeHom : α →* Matrix l l R where
  toFun := coe
  map_one' := coe_one ..
  map_mul' _ _ := coe_mul ..

end Monoid


section Instances

variable {l m R : Type*}

@[simps] -- to export `coe_def`
instance : MatrixLike (Matrix l m R) l m R where
  coe := id
  coe_injective' x y := by simp

@[simps]
instance unitaryGroup [DecidableEq l] [Fintype l] [CommRing R] [StarRing R] :
    MatrixLikeMonoid (Matrix.unitaryGroup l R) l R where
  coe x := ↑x
  coe_injective' := by simp
  coe_one := by simp
  coe_mul := by simp
-- The coercion is implemented by `Matrix.UnitaryGroup.coeMatrix`, which is defeq to `Subtype.val`
-- And indeed, `simp` uses `Subtype.val_injective`.
-- But it feels cleaner to leave it as `simp` and not overtly rely on the defeq.

@[simps]
instance unitaryGroup.diagonalSubgroup [DecidableEq l] [Fintype l] [CommRing R] [StarRing R] :
    MatrixLikeMonoid (Matrix.UnitaryGroup.diagonalSubgroup l R) l R where
  coe x := ↑↑x
  coe_injective' := by apply Function.Injective.comp <;> simp
  coe_one := by simp
  coe_mul := by simp

-- `Matrix.GeneralLinearGroup` is not implemented as a `Subtype`
@[simps]
instance GeneralLinearGroup [DecidableEq l] [Fintype l] [Semiring R] :
    MatrixLikeMonoid (Matrix.GeneralLinearGroup l R) l R where
  coe x := ↑x
  coe_injective' := Units.val_injective
  coe_one := by simp
  coe_mul := by simp

@[simps]
instance Subtype (p : Matrix l m R → Prop) : MatrixLike (Subtype p) l m R where
  coe x := ↑x
  coe_injective' := Subtype.val_injective

@[simps]
instance [DecidableEq l] [NonAssocSemiring R] [StarRing R] :
  One { H : Matrix l l R // H.IsHermitian } where one := ⟨1, Matrix.isHermitian_one⟩

@[simps]
instance Hermitian [DecidableEq l] [NonAssocSemiring R] [StarRing R] :
    MatrixLikeOne { H : Matrix l l R // H.IsHermitian } l R where
  coe x := ↑x
  coe_injective' := Subtype.val_injective
  coe_one := by simp

-- TBD: Add more.

end MatrixLike.Instances

-- TBD: Make dependent?
/-- Class for `MatrixLike` types for which coercion to `Matrix` commutes with
taking the `PiKronecker` product -/
class LawfulPiKron (α : Type*) (β : outParam Type*) (n m : outParam Type*) (R : outParam Type*)
    (ι : Type*) [Fintype ι] [CommMonoid R] [MatrixLike α n m R]
    [MatrixLike β (ι → n) (ι → m) R] where
  kron : (ι → α) → β
  commute : ∀ (f : ι → α), kron f = Matrix.PiKronecker (fun i ↦ ((f i) : Matrix n m R))

class LawfulPiKronDep (ι : Type*) [Fintype ι]
    (α : ι → Type*) (β : outParam Type*) (n m : outParam (ι → Type*)) (R : outParam Type*)
    [CommMonoid R] [∀ i, MatrixLike (α i) (n i) (m i) R] [MatrixLike β (Π i, n i) (Π i, m i) R]
    where
  kron : (Π i,  α i) → β
  commute : ∀ (f : Π i, α i), kron f = Matrix.PiKronecker (fun i ↦ ((f i) : Matrix (n i) (m i) R))

-- TBD: Will that be picked up outside of this module?
-- TBD: Why does `SetLike` use the `coe_injective'`, `coe_injective` construction?
attribute [simp, norm_cast] LawfulPiKron.commute

-- Could replace `PiKron`.
@[inherit_doc LawfulPiKron] notation3 "⨂ₗ "(...)", "r:(scoped f => LawfulPiKron.kron f) => r

namespace LawfulPiKron

section Instances

variable (n m : Type*) (R : Type*) (ι : Type*) [Fintype ι]

open Matrix

@[simps]
instance self [CommMonoid R] : LawfulPiKron (Matrix n m R) (Matrix (ι → n) (ι → m) R) n m R ι where
  kron := PiKronecker
  commute := by simp

-- TBD: The various `← piKronecker_xxx_def` below would go away if the
-- `piKronecker_mem`'s get redefined in terms of the new typeclass.

variable [DecidableEq ι] [DecidableEq n] [Fintype n]

-- Implementation note:
-- A `simp` would time out after the `apply` below.
-- The issue is that we are assuming `CommSemiring R`, but
-- `Matrix.coe_units_inv` is assuming `CommRing R`, and this somehow trips up
-- unification, which fails *very* slowly.
variable {n R ι} in
theorem isUnit_piKronecker [CommSemiring R] {G : ι → Matrix n n R} (hG : ∀ i, IsUnit (G i)) :
    IsUnit (PiKronecker G) := by
  choose G' hG' using hG
  apply IsUnit.of_mul_eq_one (PiKronecker fun i ↦ ↑(G' i)⁻¹)
  simp_rw [← piKron_matrix_def, mul_piKronecker_mul, ← hG', Units.mul_inv, piKronecker_one]

@[simps]
noncomputable instance GeneralLinearGroup [CommSemiring R] :
  LawfulPiKron (GeneralLinearGroup n R) (GeneralLinearGroup (ι → n) R) n n R ι where
  kron G := IsUnit.unit (isUnit_piKronecker (fun i ↦ Units.isUnit (G i)))
  commute f := by simp

open Matrix

@[simps]
instance unitaryGroup [CommRing R] [StarRing R] :
  LawfulPiKron (unitaryGroup n R) (unitaryGroup (ι → n) R) n n R ι where
  kron U := ⟨PiKronecker fun i ↦ ((U i) : Matrix n n R),
    by simp [← piKron_matrix_def, piKronecker_mem_unitaryGroup]⟩
  commute f := by simp

/-
This must be a non-instance, because `q` isn't a valid choice for an `outParam`
-/
variable {m ι R} in
abbrev SubtypeSquare [CommMonoid R]
    (p : Matrix m m R → Prop)
    (q : Matrix (ι → m) (ι → m) R → Prop)
    (h : (M : ι → Matrix m m R) → (∀ i, p (M i)) → (q (PiKronecker M))) :
    LawfulPiKron (Subtype p) (Subtype q) m m R ι where
  kron M := ⟨PiKronecker (fun i ↦ (M i).val), h (fun i ↦ (M i).val) (fun i ↦ (M i).property)⟩
  commute f := by simp

-- TBD: `Star R` vs `StarMul R`
@[simps]
instance Hermitian [CommMonoid R] [StarMul R] : LawfulPiKron
    { H : Matrix n n R // H.IsHermitian } { H : Matrix (ι → n) (ι → n) R // H.IsHermitian } n n R ι
  := SubtypeSquare IsHermitian IsHermitian piKronecker_isHermitian

-- The two `IsHermitian`s live in different universes:
-- set_option pp.universes true in
-- #print Hermitian -- `... IsHermitian.{u_3, u_1} IsHermitian.{u_3, max u_4 u_1} ...`

open Pi.Unitary UnitaryGroup in
@[simps]
noncomputable instance diagonalSubgroup [CommRing R] [StarRing R] :
  LawfulPiKron (diagonalSubgroup n R) (diagonalSubgroup (ι → n) R) n n R ι where
  kron U := diagonalMulEquiv fun rs ↦ ∏ i, ((diagonalMulEquiv.symm (U i)) (rs i))
  commute f := by
    simp_rw [← piKron_matrix_def, MatrixLike.unitaryGroup.diagonalSubgroup_coe,
      diagonalMulEquiv_coe_coe, SubmonoidClass.coe_finsetProd,
      ← piKronecker_diagonal (fun i k ↦ (diagonalMulEquiv.symm (f i) k : R)),
      ← diagonalMulEquiv_coe_coe, MulEquiv.apply_symm_apply] -- TBD: Nicer?

end Instances

section Basic

variable {α β n R ι : Type*}
variable [Fintype ι]

open Matrix MatrixLike

section CommMonoidWithZero

variable [CommMonoidWithZero R] [DecidableEq n] [One α] [One β]
variable [MatrixLikeOne α n R] [MatrixLikeOne β (ι → n) R] [LawfulPiKron α β n n R ι]

@[simp]
theorem PiKron_one : (⨂ₗ _ : ι, (1 : α)) = 1 := by
  apply MatrixLike.ext'
  push_cast
  simp [coe_one, ← piKron_matrix_def]

variable [DecidableEq ι]

def single (i : ι) (U : α) := ⨂ₗ j, if i = j then U else 1

theorem single_def (i : ι) (U : α) : single i U = ⨂ₗ j, if i = j then U else 1 := rfl

@[simp, norm_cast]
theorem coe_single (i : ι) (U : α) :
    ((single i U) : Matrix (ι → n) (ι → n) R) = PiKronecker (fun j ↦ if i = j then U else 1) := by
  simp [single_def, apply_ite, coe_one]

theorem single_apply_apply (i : ι) (U : α)
    (a b : ι → n) : single i U a b = if ∀ k ≠ i, a k = b k then (U (a i) (b i)) else 0 := by
  simp only [coe_single, ← piKron_matrix_def, piKronecker_apply]
  split_ifs with h
  · rw [Finset.prod_eq_single i] <;> aesop
  · obtain ⟨w, hw⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by aesop)

end CommMonoidWithZero

section CommSemiring

variable [Fintype n] [DecidableEq n] [CommSemiring R] [Monoid α] [Monoid β]
variable [DecidableEq ι]
variable [MatrixLikeMonoid α n R] [MatrixLikeMonoid β (ι → n) R] [LawfulPiKron α β n n R ι]

@[simp]
theorem mul_piKron_mul (A B : ι → α) : (⨂ₗ i, A i) * (⨂ₗ i, B i) = ⨂ₗ i, A i * B i := by
  apply MatrixLike.ext'
  simp [coe_mul, ← piKron_matrix_def, mul_piKronecker_mul]

-- TBD: higher priority than `coe_single`? is this done in general?
@[simp]
theorem single_one (i : ι) : single i (1 : α) = 1 := by
  simp [single_def]

theorem single_mul (i : ι) (x y : α) : single i (x * y) = single i x * single i y := by
  simp only [single_def]
  conv_lhs => rw [← mul_one (1 : α)]
  apply MatrixLike.ext'
  simp only [← ite_mul_ite, commute, coe_mul, ← piKron_matrix_def, mul_piKronecker_mul]

/-- Map of the `i`th factor into the Kronecker product, bundled as a monoid homomorphism -/
@[simps]
def singleHom (i : ι) : α →* β where
  toFun := single i
  map_one' := single_one i
  map_mul' := single_mul i

@[simp]
theorem commute_single {i j : ι} (h : i ≠ j) (A B : α) : Commute (single i A) (single j B) := by
  simp only [single_def, commute_iff_eq]
  apply MatrixLike.coe_injective
  simp only [coe_mul, LawfulPiKron.commute, ← piKron_matrix_def, mul_piKronecker_mul]
  grind [coe_one]

@[simp]
theorem pairwise_commute_single (f : ι → α) (s : Set ι) :
    s.Pairwise (Function.onFun Commute (fun i ↦ single i (f i))) :=
  (fun x _ y _ hneq ↦ commute_single hneq (f x) (f y))

open Finset

theorem prod_piKronecker (L : List (ι → α)) :
    (L.map (fun A ↦ ⨂ₗ i, A i)).prod = ⨂ₗ i, (L.map (Function.eval i)).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, Function.eval, ← mul_piKron_mul]
    with_reducible congr

/-- Given a function `f` from an index set `ι` to the `MatrixLikeMonoid` type `α`,
a product over `single i (f i)`s equals the tensor product of the `f i`. -/
@[simp]
theorem noncommProd_single (f : ι → α) (s : Finset ι) :
    s.noncommProd (fun i ↦ single i (f i)) (by simp) = ⨂ₗ i, if (i ∈ s) then f i else 1 := by
  induction s using cons_induction with
  | empty => simp
  | cons a s ha IH =>
    have (i : ι) : (if i = a ∨ i ∈ s then f i else 1) =
        (if a = i then f a else 1) * (if i ∈ s then f i else 1) := by grind
    simp_rw [noncommProd_cons, IH, cons_eq_insert, mem_insert, this, ← mul_piKron_mul, single_def]

theorem noncommProd_single_univ (f : ι → α) :
    univ.noncommProd (fun i ↦ single i (f i)) (by simp) = ⨂ₗ i, f i := by
  simp

end CommSemiring

end Basic

end LawfulPiKron
