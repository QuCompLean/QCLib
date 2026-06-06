/-
Copyright (c) 2025 Davood H. T. Tehrani, David Gross. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood H.T. Tehrani, David Gross
-/

module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Qml.PiTensorProduct.Equiv.Fin

/-!
# Inner Product space on PiTensorProducts indexed by Fin

This file provides the inner product space structure on PiTensorProduct spaces.

We define inner product on `⨂ i, M i` by `inner (⨂ₜ i, v i) (⨂ₜ i, w i) = ∏ i, inner (v i) (w i)`
where `v` and `w` correspond to a family of `InnerProductSpace` spaces indexed by `Fin n`
for some natural number `n`.

# Implementation note

Currently, one cannot equip `PiTensorProduct` with an `InnerProductSpace` structure
in the same way as `TensorProduct`.

For `TensorProduct`, the construction of the inner product relies on `TensorProduct.lift`,
which can `lift` sesquilinear maps. This makes it possible to define an inner product
on the tensor product space

In contrast, `PiTensorProduct.lift` does not support lifting sesquilinear maps.
Because of this limitation, the same strategy for defining an inner product
does not apply to `PiTensorProduct`. Therefore, the construction is done by induction
over the length of the `PiTensorProduct`.

-/

open PiTensorProduct
open scoped TensorProduct ComplexConjugate

@[expose] public section

universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {n} {M : Fin n → Type u} [∀ i, NormedAddCommGroup (M i)] [∀ i, InnerProductSpace 𝕜 (M i)]

@[reducible]
noncomputable def PiTensorProduct.InnerProductspace.Core :
  InnerProductSpace.Core 𝕜 (⨂[𝕜] i, M i) :=
  n.rec (motive := fun n => ∀ (M : Fin n → Type u) [∀ i, NormedAddCommGroup (M i)]
      [∀ i, InnerProductSpace 𝕜 (M i)], InnerProductSpace.Core 𝕜 (⨂[𝕜] i, M i))
    (fun M _ _ => {
      inner a b := innerₛₗ 𝕜 (isEmptyEquiv _ a) (isEmptyEquiv _ b)
      conj_inner_symm := by simp [mul_comm]
      re_inner_nonneg := by simp
      add_left := by simp
      smul_left := by simp [mul_left_comm]
      definite := by simp
    })
    (fun n ih M _ _ =>
      let ih := @ih (fun i => M i.castSucc) _ _
      letI normed := ih.toNormedAddCommGroup
      letI ips := InnerProductSpace.ofCore ih.toCore
      letI tnormed : NormedAddCommGroup ((⨂[𝕜] i : Fin n, M i.castSucc) ⊗[𝕜] M (Fin.last n)) :=
        @TensorProduct.instNormedAddCommGroup 𝕜 _ _ _ normed ips _ _
      letI tips : InnerProductSpace 𝕜 ((⨂[𝕜] i : Fin n, M i.castSucc) ⊗[𝕜] M (Fin.last n)) :=
        @TensorProduct.instInnerProductSpace 𝕜 _ _ _ normed ips _ _
      { inner := fun x y => inner 𝕜 (tmulFinSucc.symm x) (tmulFinSucc.symm y)
        conj_inner_symm := by simp
        re_inner_nonneg := by simp
        add_left x y z := by simp [inner_add_left]
        smul_left := by simp [inner_smul_left]
        definite := by simp })
    M

noncomputable instance : NormedAddCommGroup (⨂[𝕜] (i : Fin n), M i) :=
  PiTensorProduct.InnerProductspace.Core.toNormedAddCommGroup

noncomputable instance : InnerProductSpace 𝕜 (⨂[𝕜] (i : Fin n), M i) :=
  InnerProductSpace.ofCore PiTensorProduct.InnerProductspace.Core.toCore

lemma inner_def_zero {M : Fin 0 → Type*}
    [∀ i, NormedAddCommGroup (M i)] [∀ i, InnerProductSpace 𝕜 (M i)]
    (x y : ⨂[𝕜] i : Fin 0, M i) :
    inner 𝕜 x y = inner 𝕜 (isEmptyEquiv _ x) (isEmptyEquiv _ y) := rfl

lemma inner_def_succ {n : ℕ} {M : Fin (n + 1) → Type*} [∀ i, NormedAddCommGroup (M i)]
    [∀ i, InnerProductSpace 𝕜 (M i)]
    (x y : ⨂[𝕜] i : Fin (n + 1), M i) :
    inner 𝕜 x y = inner 𝕜 (tmulFinSucc.symm x) (tmulFinSucc.symm y) := rfl

@[simp] theorem inner_tprod (v w : ∀ i : Fin n, M i) :
    inner 𝕜 (⨂ₜ[𝕜] i, v i) (⨂ₜ[𝕜] i, w i) = ∏ i, inner 𝕜 (v i) (w i) := by
  induction n with
  | zero => simp [inner_def_zero]
  | succ n ih => simp [inner_def_succ, ih (fun i => v i.castSucc) (fun i => w i.castSucc),
      ← Fin.prod_univ_castSucc (fun i => inner 𝕜 (v i) (w i))]

namespace OrthonormalBasis

-- Note: Mathlib's `OrthonormalBasis` requires `[Fintype ι]`. Presumably so that sums over the basis
-- are easy to express. Mathematically, this doesn't seem necessary. Maybe one could change that?

variable {ι : Fin n → Type*} [∀ i, Fintype (ι i)]
variable (B : Π i, OrthonormalBasis (ι i) 𝕜 (M i))

noncomputable def piTensorProduct :
    OrthonormalBasis (Π i, ι i) 𝕜 (⨂[𝕜] i, M i) := Module.Basis.toOrthonormalBasis
  (Basis.piTensorProduct fun i ↦ (B i).toBasis)
  (by
    classical
    apply orthonormal_iff_ite.mpr fun k l ↦ ?_
    simp only [Basis.piTensorProduct_apply, OrthonormalBasis.coe_toBasis, inner_tprod]
    by_cases h : k = l
    · simp [h]
    · obtain ⟨i, hi⟩ : ∃ i, k i ≠ l i := by grind
      simpa [h] using Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  )

@[simp] lemma piTensorProduct_apply (k : Π i, ι i) :
    OrthonormalBasis.piTensorProduct B k = ⨂ₜ[𝕜] i, B i (k i) := by
  simp [piTensorProduct]

@[simp] lemma piTensorProduct_repr_tprod_apply (x : Π i, M i) (k : Π i, ι i) :
    (OrthonormalBasis.piTensorProduct B).repr (⨂ₜ[𝕜] i, x i) k = ∏ i, (B i).repr (x i) (k i) := by
  simp [piTensorProduct]

end OrthonormalBasis

variable [∀ i, FiniteDimensional 𝕜 (M i)]

instance : FiniteDimensional 𝕜 (⨂[𝕜] (i : Fin n), M i) :=
  Module.Basis.finiteDimensional_of_finite
    (Basis.piTensorProduct (fun i => Module.finBasis 𝕜 (M i)))

instance : CompleteSpace (⨂[𝕜] (i : Fin n), M i) :=
  FiniteDimensional.complete 𝕜 _
