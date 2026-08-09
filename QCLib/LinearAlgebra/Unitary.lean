module

public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.Lemmas
public import QCLib.LinearAlgebra.UnitaryGroup.Permutation
public import QCLib.LinearAlgebra.StdBasis
public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.PiKronecker

/-!
Work in progress
-> Define trace
-/

@[expose] public noncomputable section

variable {𝕜 E : Type*}
  [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

instance : CoeFun (unitary (E →L[𝕜] E)) (fun _ => E → E) where
  coe u := (↑u : E →L[𝕜] E)

/-- The scalar action of unitary scalars on unitary linear maps forms an `IsScalarTower`.
This allows scalar multiplication to associate with multiplication of unitary
linear maps, for example `r • (X * Z) = (r • X) * Z` from `smul_mul_assoc`.
-/
instance : IsScalarTower (unitary 𝕜) (unitary (E →L[𝕜] E)) (unitary (E →L[𝕜] E)) where
  smul_assoc r X Z := by ext; simp

/-- The action of unitary scalars on unitary linear maps satisfies
`SMulCommClass`.
This allows scalar multiplication to commute with multiplication of unitary
linear maps. In particular, `simp` can rewrite
`X * (r • Y)` as `r • (X * Y)` using `mul_smul_comm`.
-/
instance : SMulCommClass (unitary 𝕜) (unitary (E →L[𝕜] E)) (unitary (E →L[𝕜] E)) where
  smul_comm r X Z := by ext; simp

attribute [simp] smul_mul_assoc mul_smul_comm

-- Without it, certain lemmas will timeout, e.g. `controllizeRight_inv`.
instance : Inv (unitary (E →L[𝕜] E)) := inferInstance

namespace Unitary.EuclideanCLM

/-- `f` superscript stands for finite.-/
notation "𝐔ᶠ["n"]" => unitary (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)

open Matrix Equiv

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Upgrade `Matrix.UnitaryGroup.toUnitaryEuclideanCLM` to a `⋆`-isomorphism between the
unitary group of `n × n` matrices and the unitary group of continuous linear endomorphisms of
`EuclideanSpace 𝕜 n`, via the ambient star algebra equivalence `Matrix.toEuclideanCLM`. -/
@[simps! apply symm_apply]
noncomputable def unitaryGroupEquiv :
    unitaryGroup n 𝕜 ≃⋆* unitary ((EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)) :=
  Unitary.mapEquiv (StarMulEquiv.ofClass (Matrix.toEuclideanCLM (𝕜 := 𝕜)))

-- see `controllize_eq_controllizeRight_swap`
attribute [simp ←] StarMulEquiv.toMulEquiv_symm

/-- MonoidHom from phase-valued functions to diagonal unitaries -/
@[simps! -isSimp coe]
def diagonalMonoidHom :
    (n → unitary 𝕜) →⋆* unitary ((EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)) :=
  unitaryGroupEquiv.toStarMonoidHom.comp
    ⟨UnitaryGroup.diagonalMonoidHom, by intro d; apply Subtype.ext; simp⟩

@[simp]
theorem diagonalMonoidHom_apply {e j} (v : n → unitary 𝕜) :
    (diagonalMonoidHom v) e j
      = v j * e.ofLp j := by
  simp [diagonalMonoidHom, mulVec_eq_sum, diagonal_apply, mul_comm]

theorem diagonalMonoidHom_one :
    diagonalMonoidHom (fun _ : n ↦ (1 : unitary 𝕜)) = 1 := by
  ext
  simp

theorem diagonalMonoidHom_injective :
    Function.Injective (diagonalMonoidHom (n := n) (𝕜 := 𝕜)) := by
  refine (injective_iff_map_eq_one diagonalMonoidHom).mpr (fun a h ↦ ?_)
  ext x
  exact congr_fun (by simpa [Subtype.ext_iff, diagonalMonoidHom] using h) x

/-- Block-diagonal embedding of unitary operators on `EuclideanSpace 𝕜 n`, indexed by `o`,
into unitary operators on `EuclideanSpace 𝕜 (n × o)`. -/
@[simps! coe]
noncomputable def blockDiagonalStarMonoidHom {o} [Fintype o] [DecidableEq o] :
    (o → ↥(unitary (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n))) →⋆*
      ↥(unitary (EuclideanSpace 𝕜 (n × o) →L[𝕜] EuclideanSpace 𝕜 (n × o))) :=
  unitaryGroupEquiv.toStarMonoidHom.comp <|
    Matrix.UnitaryGroup.blockDiagonalStarMonoidHom.comp <|
      (StarMulEquiv.piCongrRight fun _ : o => unitaryGroupEquiv.symm).toStarMonoidHom

@[simps!]
def reindexMonoidEquiv {m} [DecidableEq m] [Fintype m] (e : m ≃ n) :
    ↥(unitary (EuclideanSpace 𝕜 m →L[𝕜] EuclideanSpace 𝕜 m)) ≃*
      ↥(unitary (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)) :=
  unitaryGroupEquiv.symm.toMulEquiv.trans <|
    (Matrix.reindexMonoidEquiv e).trans unitaryGroupEquiv.toMulEquiv

variable (𝕜) in
/-- Permutations of basis vectors as continuous linearmaps. -/
@[simps! -isSimp apply]
def permHom : Perm n →* unitary ((EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)) :=
  unitaryGroupEquiv.toMonoidHom.comp (UnitaryGroup.permHom 𝕜 (n := n))

@[simp]
theorem permHom_apply_basis (i : n) (σ : Perm n) :
    permHom ℂ σ δ[i] = δ[σ i] := by
  ext
  simp [permHom_apply, basisVector_def]
  grind

-- mpr is added to make usage of `a = b` that appears as a hypothesis more convenient.
omit [DecidableEq n] in
theorem ContinuousLinearMap.ext_basis_iff
    {a b : unitary ((EuclideanSpace ℂ n) →L[ℂ] (EuclideanSpace ℂ n))} :
    (∀ i : n, a δ[i] = b δ[i]) ↔ a = b := by
  refine ⟨fun h => ?_, fun i => ?_⟩
  · ext v : 2
    rw [← (EuclideanSpace.basisFun n ℂ).sum_repr v]
    simp_rw [basisVector_def] at h
    simp [h]
  · simp_all

theorem permHom_injective : Function.Injective (permHom (n := n) ℂ) := by
  intro σ τ h
  ext i
  simp only [← ContinuousLinearMap.ext_basis_iff, permHom_apply_basis] at h
  apply Module.Basis.injective (EuclideanSpace.basisFun n ℂ).toBasis
  simpa [basisVector_def] using (h i)

end Unitary.EuclideanCLM


section PiOuterProduct

open PiOuterProduct Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ι → Type*} [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
variable {𝕜 : Type*} [RCLike 𝕜]

namespace EuclideanCLM -- All of this redundancy for a single lemma: `piTprod_coe`

variable (U V : Π i, (EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i)))

/-- Tensor product of a family of Euclidean continuous linear maps. -/
instance :
    PiOuterProduct
      (fun i ↦ EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i))
      (EuclideanSpace 𝕜 (Π i, n i) →L[𝕜] EuclideanSpace 𝕜 (Π i, n i)) where
  tprod U := toEuclideanCLM (𝕜 := 𝕜) (⨂ i, (toEuclideanCLM (𝕜 := 𝕜)).symm (U i))

theorem piTprod_def
    (U : Π i, EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i)) :
    (⨂ i, U i) =
      toEuclideanCLM (𝕜 := 𝕜) (⨂ i, (toEuclideanCLM (𝕜 := 𝕜)).symm (U i)) := rfl

@[simp]
theorem piTprod_apply
    (U : Π i, EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i))
    (v : EuclideanSpace 𝕜 (Π i, n i)) :
    (⨂ i, U i) v =
      (⨂ i, (toEuclideanCLM (𝕜 := 𝕜)).symm (U i)).mulVec v := by
  simp [piTprod_def]

@[simp]
theorem mul_piTprod_mul
    (U V : Π i, EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i)) :
    (⨂ i, U i) * (⨂ i, V i) = ⨂ i, U i * V i := by
  ext
  simp [mul_piKronecker_mul]

@[simp]
theorem piTprod_one : (⨂ i, (1 :
    (EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i)))) = 1 := by
  ext
  simp

theorem piTprod_smul_univ (c : ι → 𝕜) :
    (⨂ i, c i • U i) = (∏ i, c i) • (⨂ i, U i) := by
  ext
  simp [piKronecker_smul_univ, Matrix.smul_mulVec]

end EuclideanCLM

open EuclideanCLM

namespace Unitary.EuclideanCLM

variable (U V : Π i, unitary (EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i)))

/-- `star` distributes over the tensor product of CLMs (via `toEuclideanCLM` being a
`StarAlgEquiv`, reduced to the matrix-level fact about `piKronecker`). -/
@[simp]
theorem star_piTprod_clm
    (U : Π i, EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i)) :
    star (⨂ i, U i) = ⨂ i, star (U i) := by
  ext
  simp [piTprod_def, ← map_star, star_piKronecker]

/-- The tensor product of a family of unitary CLMs is unitary. -/
theorem piTprod_unitary
    (U : Π i, EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i))
    (hU : ∀ i, U i ∈ unitary (EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i))) :
    (⨂ i, U i) ∈ unitary (EuclideanSpace 𝕜 (Π i, n i) →L[𝕜] EuclideanSpace 𝕜 (Π i, n i)) := by
  simp_all [mem_iff, star_piTprod_clm, piTprod_one, and_self]

-- This instance could be also defined by `unitaryGroupEquiv (⨂ i, unitaryGroupEquiv.symm (U i))`
-- However, it would make proving `piTprod_coe`, `piTprod_smul_univ` more complicated.
/-- Tensor product of a family of unitary CLMs, via `unitaryGroupEquiv`. -/
instance :
    PiOuterProduct (fun i ↦ unitary (EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i)))
      (unitary (EuclideanSpace 𝕜 (Π i, n i) →L[𝕜] EuclideanSpace 𝕜 (Π i, n i))) where
    tprod U := ⟨(⨂ i, (U i).val), by simp [piTprod_unitary]⟩

theorem piTensor_def :
  (⨂ i, U i) = ⟨(⨂ i, (U i).val), by simp [piTprod_unitary]⟩ := by rfl

@[simp]
theorem piTprod_apply (v : EuclideanSpace 𝕜 (Π i, n i)) :
    (⨂ i, U i) v =
      (⨂ i, unitaryGroupEquiv.symm (U i) : Matrix (Π i, n i) (Π i, n i) 𝕜).mulVec v := by
  simp [PiOuterProduct.tprod]

@[simp]
theorem mul_piTprod_mul :
    (⨂ i, U i) * (⨂ i, V i) = ⨂ i, U i * V i := by
  simp [piTensor_def]

@[simp]
theorem piTprod_one : (⨂ i, (1 : unitary
    (EuclideanSpace 𝕜 (n i) →L[𝕜] EuclideanSpace 𝕜 (n i)))) = 1 := by
  simp [piTensor_def]

@[simp]
theorem piTprod_inv :
    (⨂ i, U i)⁻¹ = ⨂ i, (U i)⁻¹ :=
  inv_eq_of_mul_eq_one_left (by simp)

@[simp]
theorem piTprod_coe :
    (⨂ i, U i).val = (⨂ i, (U i).val) := by
  simp [piTprod_def, Unitary.EuclideanCLM.piTensor_def]

-- Combining simps causes timeout, investigate why
theorem piTprod_smul_univ (c : ι → unitary 𝕜) :
    (⨂ i, c i • U i) = (∏ i, c i) • (⨂ i, U i) := by
  simp [piTensor_def, Subtype.ext_iff]
  simp [Submonoid.smul_def, _root_.EuclideanCLM.piTprod_smul_univ]

end Unitary.EuclideanCLM

end PiOuterProduct
