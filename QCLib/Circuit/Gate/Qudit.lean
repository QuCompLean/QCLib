module

public import QCLib.LinearAlgebra.StdBasis
public import QCLib.LinearAlgebra.Unitary
public import QCLib.LinearAlgebra.UnitaryGroup.RootsOfUnity
public import Mathlib.Analysis.Fourier.ZMod


@[expose] public noncomputable section

open Unitary Matrix ContinuousLinearMap

variable (d : ℕ)

attribute [simp ←] map_pow

notation "𝐔ᶠ["n"]" => unitary (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)

/-- Clock Operator on a qudit. -/
def Z : 𝐔ᶠ[Fin d] := diagonalMonoidHom (fun k => (uζ d) ^ (k : ℕ))

/-- Shift Operator on a qudit. -/
def X : 𝐔ᶠ[Fin d] := permHom ℂ (finRotate d)

@[simp]
theorem Z_apply (k : Fin d) : (Z d) δ[k] = ((ζ d) ^ (k : ℕ)) • δ[k] := by
  ext
  simp [Z, basisVector_def]
  grind

@[simp]
theorem inv_Z_apply (k : Fin d) : (Z d)⁻¹ δ[k] = ((ζ d) ^ (- k : ℤ)) • δ[k] := by
  ext
  simp [← Unitary.star_eq_inv, Z, ← map_star, ζ_star, basisVector_def]
  grind

/- Since `*_apply` lemmas are expressed for `ContinuousLinearMap`s, the automatic coercion
  of `ContinuousLinearMap` to plain functions should be prevented, otherwise simp will not fire.
-/
attribute [-simp] coe_comp' coe_pow' coe_mul'
attribute [simp] ContinuousLinearMap.mul_def ContinuousLinearMap.comp_apply

@[simp]
theorem Z_pow_apply (k : Fin d) (m : ℤ) :
    ((Z d) ^ m) δ[k] = ((ζ d) ^ (k : ℕ)) ^ m • δ[k] := by
  ext
  simp [Z, ← map_zpow, basisVector_def,   coe_zpow]
  grind

@[simp]
theorem Z_pow [NeZero d] : (Z d) ^ d = 1 := by
  ext
  simp [Z, pow_right_comm]

@[simp]
theorem orderOf_Z [hd : d.AtLeastTwo] : orderOf (Z d) = d :=
  (orderOf_eq_iff hd.toNeZero.pos).mpr (by
    simp only [Z_pow, ne_eq, true_and]
    intro m hmd hm h
    apply ((orderOf_eq_iff hd.toNeZero.pos).mp (orderOf_uζ d)).right m hmd hm
    rw [Z, ← diagonalMonoidHom_one, ← map_pow,
      Function.Injective.eq_iff diagonalMonoidHom_injective] at h
    simpa [Nat.mod_eq_of_lt hd.one_lt] using congrFun h 1
  )

@[simp]
theorem X_apply (k : Fin d) [NeZero d] : (X d) δ[k] = δ[(k + 1)] := by
  ext
  simp [X, basisVector_def, permHom_apply, UnitaryGroup.toUnitaryEuclideanCLM_coe]
  grind

@[simp]
theorem inv_X_apply (k : Fin d) [NeZero d] : (X d)⁻¹ δ[k] = δ[(k - 1)] := by
  rw [← show (X d) δ[(k - 1)] = δ[k] by simp,
    ← ContinuousLinearMap.comp_apply, ← mul_def]
  norm_cast
  simp

theorem orderOf_finRotate [hd : d.AtLeastTwo] :
    orderOf (finRotate d) = d := by
  simp [(isCycle_finRotate_of_le hd.prop).orderOf, support_finRotate_of_le hd.prop]

@[simp]
theorem X_pow [hd : d.AtLeastTwo] : (X d) ^ d = 1 := by
  simp [X, ((orderOf_eq_iff hd.toNeZero.pos).mp (orderOf_finRotate d)).left]

@[simp]
theorem orderOf_X [hd : d.AtLeastTwo] : orderOf (X d) = d :=
  (orderOf_eq_iff hd.toNeZero.pos).mpr (by
    simp only [X_pow, ne_eq, true_and]
    intro m hmd hm h
    apply ((orderOf_eq_iff hd.toNeZero.pos).mp (orderOf_finRotate d)).right m hmd hm
    apply permHom_injective
    simpa [X] using h
  )

theorem Z_X_anticomm [hd : NeZero d] : (Z d) * (X d) = (uζ d) • (X d) * (Z d) := by
  apply ContinuousLinearMap.ext_basis_iff.mp (fun i ↦ ?_)
  simp [← pow_succ']

section DFT

variable [NeZero d]

section aux

open ComplexConjugate ZMod Complex Real

@[simp]
theorem finEquiv_val (a : Fin d) :
    (finEquiv d a).val = ↑a := by
  cases d with
  | zero => exact Fin.elim0 a
  | succ n => rfl

open AddChar in
theorem stdChar_orthogonal (t s : ZMod d) :
    ∑ x, stdAddChar (t * x) * conj (stdAddChar (s * x)) = if t = s then ↑d else 0 := by
  simp [← inv_apply_eq_conj, ← inv_apply', ← map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, mul_comm,
    sum_mulShift _ (isPrimitive_stdAddChar d), sub_eq_zero]

/-- The matrix representation of the inverse DFT for `ZMod N`, also known as the *Schur matrix* -/
def Matrix.idftZMod : Matrix (ZMod d) (ZMod d) ℂ :=
  of fun i j ↦ conj ((dft (Pi.single j 1)) i)

@[simp]
theorem Matrix.idftZMod_apply_apply (i j : ZMod d) : idftZMod d i j = stdAddChar (i * j) := by
  simp [idftZMod, ← AddChar.map_neg_eq_conj, dft_apply, Pi.single_apply, mul_comm]

/-- The inverse DFT for `ZMod N`, normalized and bundled as a unitary matrix
with index type `ZMod N` -/
@[simps coe]
def UnitaryGroup.idftZMod : 𝐔[ZMod d] := ⟨√(d⁻¹) • Matrix.idftZMod d, by
  simp only [Real.sqrt_inv, mem_unitaryGroup_iff, star_smul, star_trivial, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, smul_assoc_symm, smul_eq_mul,
    show (√↑d)⁻¹ * (√↑d)⁻¹ = (d : ℝ)⁻¹ by grind]
  ext
  simp [Matrix.mul_apply, Matrix.one_apply, stdChar_orthogonal] ⟩

/-- The inverse DFT for `ZMod N`, normalized and bundled as a unitary matrix
with index type `Fin N` -/
@[simps! -isSimp coe]
def UnitaryGroup.idftFin : 𝐔[Fin d] :=
  reindexMonoidEquiv (ZMod.finEquiv d).symm (idftZMod d)

@[simp]
theorem UnitaryGroup.idftFin_apply (a b) : idftFin d a b = √d⁻¹ • ζ d ^ (a * b : ℕ) := by
  simp [idftFin_coe, stdAddChar_apply, toCircle_apply, ← map_mul, ← div_mul_eq_mul_div,
    Complex.exp_nat_mul', show cexp (2 / d * ↑π * I) = ζ d by grind [ζ_def], ζ_pow_mul]

end aux


/- Refer to `https://arxiv.org/pdf/2607.06675` for sign convention. -/
/-- Quantum Fourier transformation for a single qudit. For d = 2, it reduces to Hadamard gate. -/
def 𝓕 : 𝐔ᶠ[Fin d] :=
  UnitaryGroup.toUnitaryEuclideanCLM (UnitaryGroup.idftFin d)

@[simp]
theorem 𝓕_apply (v) : 𝓕 d δ[v] = ∑ k : Fin d, ((√d⁻¹ : ℂ) * (ζ d ^ (k * v : ℕ))) • δ[k] := by
  ext
  simp [𝓕, basisVector_def, UnitaryGroup.toUnitaryEuclideanCLM_coe, Pi.single_apply]

@[simp]
theorem 𝓕_mul_Z_eq_X_mul_𝓕 : 𝓕 d * X d = Z d * 𝓕 d := by
  apply ContinuousLinearMap.ext_basis_iff.mp (fun i ↦ ?_)
  simp [mul_assoc, ← pow_add, ← mul_add_one]
  simp [pow_mul']

@[simp]
theorem 𝓕_conj_X : 𝓕 d * X d * (𝓕 d)⁻¹ = Z d := by
  simp

@[simp]
theorem 𝓕_conj_Z : (𝓕 d)⁻¹ * Z d * 𝓕 d = X d := by
  simp [mul_assoc, ← 𝓕_mul_Z_eq_X_mul_𝓕]


-- def 𝓓 (k m : ℤ) : 𝐔ᶠ[Fin d] := (star (uζ (2 * d))) ^ (k * m) • Z d ^ k * X d ^ m

-- theorem 𝓕_conj_𝓓 (k m : ℤ) (h₁ : |k| ≤ d) (h₂ : |m| ≤ d) :
--     𝓕 d * 𝓓 d k m * (𝓕 d)⁻¹ = 𝓓 d (-k) m := by
--   rw [←mul_left_inj (𝓕 d), inv_mul_cancel_right]
--   apply ContinuousLinearMap.ext_basis_iff.mp (fun i ↦ ?_)
--   simp [𝓓]
