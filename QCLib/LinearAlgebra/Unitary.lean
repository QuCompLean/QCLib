module

public import QCLib.Mathlib.LinearAlgebra.UnitaryGroup.Lemmas
public import QCLib.LinearAlgebra.UnitaryGroup.Permutation
public import QCLib.LinearAlgebra.StdBasis

@[expose] public noncomputable section

instance {𝕜 E}
    [Semiring 𝕜] [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E] [StarMul (E →L[𝕜] E)]
    : CoeFun (unitary (E →L[𝕜] E)) (fun _ => E → E) where
  coe u := (↑u : E →L[𝕜] E)

open Matrix Equiv

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {𝕜 : Type*} [RCLike 𝕜]

@[simp]
theorem Matrix.toEuclideanLinCLM_mem_unitary (U : Matrix.unitaryGroup n 𝕜) :
    (toEuclideanCLM (n := n) (𝕜 := 𝕜) (U : Matrix n n 𝕜)) ∈
      unitary ((EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)) := by
  rw [Unitary.mem_iff]
  constructor <;> simp [← StarHomClass.map_star, ← map_mul]

@[simps -isSimp coe]
def Matrix.UnitaryGroup.toUnitaryEuclideanCLM :
    unitaryGroup n 𝕜 →⋆* unitary ((EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)) where
  toFun U := ⟨Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜) U, by simp⟩
  map_one' := by simp
  map_mul' := by simp
  map_star' := by intros; ext1; simp [StarHomClass.map_star]

namespace Unitary

def diagonalMonoidHom :
    (n → unitary 𝕜) →⋆* unitary ((EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)) :=
  (Unitary.map (StarMonoidHom.ofClass (toEuclideanCLM (𝕜 := 𝕜)))).comp
    ⟨UnitaryGroup.diagonalMonoidHom, by intro d; apply Subtype.ext; simp⟩

@[simp]
theorem diagonalMonoidHom_apply {e j} (v : n → unitary 𝕜) :
    ((Unitary.diagonalMonoidHom v) : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n) e j
      = v j * e.ofLp j := by
  simp [Unitary.diagonalMonoidHom, mulVec_eq_sum, diagonal_apply, mul_comm]

theorem diagonalMonoidHom_one :
    Unitary.diagonalMonoidHom (fun _ : n ↦ (1 : unitary 𝕜)) = 1 := by
  ext
  simp

theorem diagonalMonoidHom_injective :
    Function.Injective (Unitary.diagonalMonoidHom (n := n) (𝕜 := 𝕜)) := by
  refine (injective_iff_map_eq_one Unitary.diagonalMonoidHom).mpr (fun a h ↦ ?_)
  ext x
  exact congr_fun (by simpa [Subtype.ext_iff, Unitary.diagonalMonoidHom] using h) x

variable (𝕜) in
/-- Permutations of basis vectors as continuous linearmaps. -/
@[simps! -isSimp apply]
def permHom : Perm n →* unitary ((EuclideanSpace 𝕜 n) →L[𝕜] (EuclideanSpace 𝕜 n)) :=
  UnitaryGroup.toUnitaryEuclideanCLM.toMonoidHom.comp (UnitaryGroup.permHom 𝕜 (n := n))

@[simp]
theorem permHom_apply_basis (i : n) (σ : Perm n) :
    permHom ℂ σ δ[i] = δ[σ i] := by
  ext
  simp [permHom_apply, basisVector_def, UnitaryGroup.toUnitaryEuclideanCLM_coe]
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
