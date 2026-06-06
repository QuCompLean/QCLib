/-
Copyright (c) 2025 Davood H. T. Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood H.T. Tehrani, David Gross
-/

module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open PiTensorProduct Fin
open scoped TensorProduct

@[expose] public section

namespace PiTensorProduct

section tmulFinSumEquiv

variable {n m} {R : Type*} {M : Fin (n + m) → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Isomorphism between product of tensors indexed by `{1, ..., n} ⊆ Fin (n+m)`
and `{n+1, ..., m} ⊆ Fin (n+m)`, and tensors indexed by `Fin (n + m)`. -/
def tmulFinSumEquiv :
    ((⨂[R] (i₁ : Fin n), M (castAdd m i₁)) ⊗[R] (⨂[R] (i₂ : Fin m), M (natAdd n i₂)))
      ≃ₗ[R] ⨂[R] (i : Fin (n + m)), M i :=
  (tmulEquivDep R (fun i => M (finSumFinEquiv i))).trans
    (reindex R (fun i => M i) (finSumFinEquiv.symm)).symm

@[simp]
theorem tmulFinSumEquiv_tprod
    (lv : (i : Fin n) → M ⟨i, by omega⟩) (rv : (i : Fin m) → M ⟨n + i, by omega⟩) :
      tmulFinSumEquiv ((⨂ₜ[R] i, lv i) ⊗ₜ (⨂ₜ[R] i : Fin m, rv i))
        = ⨂ₜ[R] i : Fin (n + m), addCases lv rv i := by
  simp only [tmulFinSumEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  erw [reindex_tprod, tmulEquivDep_apply]
  congr with x
  aesop

@[simp]
theorem tmulFinSumEquiv_symm_tprod (av : (i : Fin (n + m)) → M i) :
    (tmulFinSumEquiv).symm (⨂ₜ[R] i, av i) =
      (⨂ₜ[R] i : Fin n, av (castAdd m i)) ⊗ₜ[R] (⨂ₜ[R] i : Fin m, av (natAdd n i)) := by
  simp only [tmulFinSumEquiv, LinearEquiv.trans_symm, LinearEquiv.trans_apply]
  erw [reindex_tprod finSumFinEquiv.symm]
  erw [tmulEquivDep_symm_apply]
  simp

end tmulFinSumEquiv

section tmulFinSuccEquiv

variable {n : Nat} {R : Type*} {M : Fin (n.succ) → Type*}
variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

def tmulFinSucc :
    (⨂[R] i : Fin n, M (castSucc i)) ⊗[R] (M (last n)) ≃ₗ[R] ⨂[R] (i : Fin n.succ), M i :=
  (tmulFinSumEquiv.symm ≪≫ₗ
    (TensorProduct.congr (LinearEquiv.refl _ _) (subsingletonEquiv 0))).symm

@[simp]
theorem tmulFinSucc_tprod (f : (i : Fin n) → M (castSucc i)) (x : M (last n)) :
    haveI := decidableEq_of_subsingleton (α := Fin 1)
    tmulFinSucc ((⨂ₜ[R] i, f i) ⊗ₜ[R] x)
      = ⨂ₜ[R] (i : Fin (n + 1)), addCases f (Pi.single 0 x) i := by
  erw [tmulFinSucc, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, TensorProduct.congr_symm_tmul, tmulFinSumEquiv_tprod]
  rfl

@[simp]
theorem tmulFinSucc_symm (f : (i : Fin n.succ) → M i) :
    tmulFinSucc.symm (⨂ₜ[R] i, f i) = (⨂ₜ[R] i, f (castSucc i)) ⊗ₜ[R] f (last n) := by
  simp only [Nat.succ_eq_add_one, tmulFinSucc, isValue, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, tmulFinSumEquiv_symm_tprod]
  erw [TensorProduct.congr_tmul, LinearEquiv.refl_apply, subsingletonEquiv_apply_tprod]
  congr

end tmulFinSuccEquiv

section tuple
open Module

variable {n m} {p q} {R : Type*} [CommSemiring R]
  (b : Fin m → Basis (Fin n) R (Fin n → R)) (b' : Fin p → Basis (Fin q) R (Fin q → R))

noncomputable def tupleEquiv :
    (⨂[R] _ : Fin m, (Fin n → R)) ≃ₗ[R] (Fin m → Fin n) → R :=
  (Basis.piTensorProduct b).equivFun

@[simp]
theorem tupleEquiv_tprod (f : Fin m → Fin n → R) :
    tupleEquiv b (tprod R f) = fun j => ∏ i, (b i).repr (f i) (j i) := by
  ext j
  simp [tupleEquiv]

@[simp]
theorem tupleEquiv_symm_single :
    ∀ j, (tupleEquiv b).symm (Pi.single j 1) = ⨂ₜ[R] i, b i (j i) := by
  intro j
  simp only [LinearEquiv.symm_apply_eq, tupleEquiv_tprod, Basis.repr_self]
  ext k
  by_cases h : k = j
  · rw [h]
    simp
  · obtain ⟨i, hi⟩ : ∃ i, j i ≠ k i := by grind
    rw [Finset.prod_eq_zero (Finset.mem_univ i)] <;> simp_all

noncomputable def matrixEquiv :
    Matrix (Fin m → Fin n) (Fin p → Fin q) R ≃ₗ[R]
      (⨂[R] _ : Fin p, (Fin q → R)) →ₗ[R] (⨂[R] _ : Fin m, (Fin n → R)) :=
  Matrix.toLin (Basis.piTensorProduct b') (Basis.piTensorProduct b)

@[simp]
theorem matrixEquiv_apply (M : Matrix (Fin m → Fin n) (Fin p → Fin q) R)
    (x : ⨂[R] _ : Fin p, (Fin q → R)) :
    matrixEquiv b b' M x =
      ∑ j, M.mulVec ((Basis.piTensorProduct b').repr x) j • ⨂ₜ[R] i, b i (j i) := by
  simp [matrixEquiv, Matrix.toLin_apply]

@[simp]
theorem matrixEquiv_symm_apply (i : Fin m → Fin n) (j : Fin p → Fin q)
    (f : (⨂[R] _ : Fin p, (Fin q → R)) →ₗ[R] (⨂[R] _ : Fin m, (Fin n → R))) :
    ((matrixEquiv b b').symm f i j) =
      (Basis.piTensorProduct b).repr (f (Basis.piTensorProduct b' j)) i := by
  simp [matrixEquiv, LinearMap.toMatrix_apply]


end tuple
end PiTensorProduct

