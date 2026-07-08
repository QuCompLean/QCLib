/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani, George Afentakis
-/

import QCLib.Circuit.Gate.Qubit
import QCLib.Circuit.Hadamard
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

open Matrix Qubit EuclideanSpace Module Real Orientation


attribute [instance 10000] instModuleForall


variable {n}
variable (f : Register n → Fin 2)

-- Oracle is identical to DJ
def oracle : 𝐔[Register n] :=
⟨diagonal (fun k ↦ (-1 : ℂ)^((f k) : ℕ)), by simp [Unitary.mem_iff, ← pow_add]⟩


/-- The uniform superposition over all basis states orthogonal to `ω`. -/
noncomputable def sPerp (ω : Register n) : Register n → ℂ :=
  (Real.sqrt (2^n - 1) : ℂ)⁻¹ • ∑ k ∈ Finset.univ.filter (· ≠ ω), δ[k]

/-- The reflection around the zero state, which is `2|0><0| - I` -/
def zeroRefl (n : ℕ) : 𝐔[Register n] :=
    ⟨diagonal (fun k : Register n ↦ (-1 : ℂ) ^ (if k = 0 then 0 else 1 : ℕ)),
      by constructor <;> simp [ext,diagonal_apply] <;> aesop⟩

/-- The Grover diffusion operator `H (2|0⟩⟨0| - I) H`. -/
noncomputable def diffusion (n : ℕ) : 𝐔[Register n] := (HH n) * (zeroRefl n) * (HH n)

noncomputable def groverIterate : 𝐔[Register n] := diffusion n * oracle f

/-- The state after `r` Grover iterates applied to the initial uniform superposition. -/
noncomputable def grover (r : ℕ) : (Register n → ℂ) :=
  (groverIterate f) ^ r • (HH n • δ[0])

noncomputable def groverTheta (n : ℕ) : ℝ :=
  Real.arcsin ((Real.sqrt 2)⁻¹ ^ n)

/-- The basis vector orthogonal to the uniform superposition `HH n • δ[0]`. Part of the diffusion
 operator's eigenbasis `{HH n • δ[0], perp ω}`. -/
noncomputable def perp (ω : Register n) : Register n → ℂ :=
  (Real.cos (groverTheta n) : ℂ) • δ[ω] - (Real.sin (groverTheta n) : ℂ) • sPerp ω

/-- Flips the first coordinate of a 2D vector. -/
def reflectTarget (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) := !₂[-v 0, v 1]

private noncomputable def groverOrientation : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  -(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

/-- Expresses the state in the 2D `(δ[ω], sPerp ω)` coordinate frame -/
noncomputable def coord (ω : Register n) (v : EuclideanSpace ℝ (Fin 2)) : Register n → ℂ :=
  (v 0 : ℂ) • δ[ω] + (v 1 : ℂ) • sPerp ω

private lemma groverOrientation_areaForm (x y : EuclideanSpace ℝ (Fin 2)) :
    groverOrientation.areaForm x y = x 1 * y 0 - x 0 * y 1 := by
  simp [groverOrientation, Orientation.areaForm_neg_orientation,
    Orientation.volumeForm_robust _ (EuclideanSpace.basisFun (Fin 2) ℝ) rfl, Basis.det_apply,
    Orientation.areaForm_to_volumeForm, det_fin_two, Basis.toMatrix_apply]
  ring_nf

-- computes the 90° rotation operator
private lemma groverOrientation_rightAngle (v : EuclideanSpace ℝ (Fin 2)) :
    groverOrientation.rightAngleRotation v = !₂[v 1, -v 0] := by
  apply ext_inner_left ℝ
  intro w
  rw [Orientation.inner_rightAngleRotation_right, groverOrientation_areaForm,PiLp.inner_apply]
  simp
  ring

private lemma groverOrientation_rotation_comp (α θ : ℝ) :
    groverOrientation.rotation (θ : Real.Angle) !₂[Real.sin α, Real.cos α] =
  !₂[Real.sin (α + θ), Real.cos (α + θ)] := by
  matrix_expand [Orientation.rotation_apply,groverOrientation_rightAngle,Real.sin_add, Real.cos_add]

theorem oracle_apply (k : Register n) : oracle f • δ[k] = (-1)^ ((f k) : ℕ) • δ[k] := by
  simp [funext_iff,oracle, basisVector_def,Submonoid.smul_def]
  grind

lemma uniform_decomp (ω : Register n) :
    HH n • δ[0] = (√2 : ℂ)⁻¹^n • δ[ω] + (√2 : ℂ)⁻¹^n • ∑ k ∈ Finset.univ.filter (· ≠ ω), δ[k] := by
  simp_rw [HH_apply,HadamardBasisVector,basisVector_def]
  aesop


lemma zeroRefl_entry (j k : Register n) :(zeroRefl n).val j k =
      if j = k then (-1 : ℂ)^(if j = 0 then 0 else 1) else 0 := by
  rw [zeroRefl]
  aesop

lemma oracle_apply_omega {ω} (hω : f ω = 1) : oracle f • δ[ω] = -δ[ω] := by
  simp [oracle_apply,hω]

lemma zeroRefl_diagonal : (zeroRefl n).val = diagonal (fun x ↦ if x = 0 then 1 else -1) := by
  ext i j
  rw [zeroRefl_entry]
  aesop

lemma zeroRefl_smul_eq (r : Register n → ℂ) :
    (zeroRefl n) • r = (2 * r 0) • δ[0] - r := by
  simp [funext,Submonoid.smul_def,zeroRefl_diagonal,mulVec_diagonal,basisVector_def]
  grind

-- plus one eigenvalue
lemma diffusion_fixes_uniform :
    (diffusion n) • (HH n • δ[0]) = HH n • δ[(0 : Register n)] := by
  rw [diffusion,SemigroupAction.mul_smul, SemigroupAction.mul_smul]
  with_reducible_and_instances congr 1
  simp [← SemigroupAction.mul_smul (HH n) (HH n),HH_sq,zeroRefl_smul_eq, basisVector_def, two_smul]

--- Math helper lemmas (extracting them like this keeps the ugliness contained)
private lemma sqrt_two_inv_le_one : (√2 : ℝ)⁻¹ ≤ 1 :=
  inv_le_one_of_one_le₀ (by norm_num [← Real.sqrt_one,Real.sqrt_le_sqrt])

private lemma sqrt_two_pow_sub_sq (n : ℕ) :
    (Real.sqrt (2^n - 1) : ℂ)^2 = (2^n - 1 : ℂ) := by
  have: 1  ≤ 2^n := by exact Nat.one_le_two_pow
  norm_cast
  grind

private lemma amp_sq (n : ℕ) : ((√2)⁻¹ ^ n) ^ 2 = 1 / 2 ^ n := by
  rw [← pow_mul, mul_comm, pow_mul, inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      inv_pow, one_div]

private lemma amp_sq_mul_two_pow (n : ℕ) : ((√2)⁻¹ ^ n) ^ 2 * 2 ^ n = 1 := by
  rw [amp_sq, one_div, inv_mul_cancel₀ (by positivity)]

private lemma sqrt_two_pow_sub_ne_zero (n : ℕ) (hn : n ≠ 0) :
    (Real.sqrt (2^n - 1) : ℂ) ≠ 0 := by
  have: (1 : ℝ) < 2^n := by exact_mod_cast Nat.one_lt_two_pow_iff.mpr hn
  grind [Complex.ofReal_ne_zero.mpr,Real.sqrt_ne_zero'.mpr]
-----------------------------------------------------------------------


--- Useful trigonometric lemmas specifically for groverTheta
lemma sin_groverTheta_eq (n : ℕ) : Real.sin (groverTheta n) = (Real.sqrt 2)⁻¹ ^ n := by
  rw [groverTheta,Real.sin_arcsin]
  · linarith [pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg 2)) n]
  · exact pow_le_one₀ (by positivity) sqrt_two_inv_le_one

lemma cos_groverTheta_eq (n : ℕ) :
    Real.cos (groverTheta n) = (√2)⁻¹ ^ n * √(2 ^ n - 1) := by
  rw [groverTheta,Real.cos_arcsin, ← Real.sqrt_sq (by positivity : (0:ℝ) ≤ (√2)⁻¹ ^ n),
      ← Real.sqrt_mul (by positivity),Real.sq_sqrt (by positivity)]
  with_reducible_and_instances congr 1
  nlinarith [amp_sq n, amp_sq_mul_two_pow n]


lemma groverTheta_pos : 0 < groverTheta n := by
  rw [groverTheta, Real.arcsin_pos]; positivity

lemma groverTheta_le (hn : n ≠ 0) : groverTheta n ≤ π / 4 := by
  rw [groverTheta,← Real.arcsin_sin (by linarith [Real.pi_pos])
    (show π/4 ≤ π/2 by linarith [Real.pi_pos]),Real.sin_pi_div_four]
  apply Real.monotone_arcsin
  rw [show √2/2 = (√2)⁻¹ by grind]
  exact pow_le_of_le_one (by positivity) sqrt_two_inv_le_one hn
-------------------------------------------------------------------------


lemma sPerp_apply (ω k : Register n) :
    sPerp ω k = if k = ω then 0 else (Real.sqrt ((2^n - 1 : ℕ) : ℝ) : ℂ)⁻¹ := by
  simp [sPerp,basisVector_def]

lemma oracle_apply_sPerp (ω : Register n)
    (hb : ∀ k, k ≠ ω → f k = 0) : oracle f • sPerp ω = sPerp ω := by
  rw [sPerp, smul_comm,Submonoid.smul_def, smul_eq_mulVec, mulVec_sum]
  with_reducible_and_instances congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  simpa [Submonoid.smul_def, hb k (by simpa using hk)] using oracle_apply f k

lemma diffusion_reflection (v : Register n → ℂ) :
    (diffusion n) • v = (2 * ((√2)⁻¹ : ℂ)^n * ∑ k, v k) • (HH n • δ[0]) - v := by
  simp_rw [diffusion, SemigroupAction.mul_smul, zeroRefl_smul_eq, HH_smul_zero_apply, smul_sub,
    ← SemigroupAction.mul_smul, HH_sq, one_smul, smul_comm (HH n )]

lemma sum_sPerp (ω : Register n) :
    ∑ k, sPerp ω k = (Real.sqrt (2^n - 1))⁻¹ * (2^n - 1) := by
  simp only [sPerp, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum,Finset.sum_apply]
  rw [Finset.sum_comm]
  simp [basisVector_def, Pi.basisFun_apply,  Finset.filter_ne']

lemma uniform_decomp_orthonormal (ω : Register n) (hn : n ≠ 0) :
    HH n • δ[0] = Real.sin (groverTheta n) • δ[ω] + Real.cos (groverTheta n) • sPerp ω := by
  norm_num [uniform_decomp ω, sin_groverTheta_eq, cos_groverTheta_eq,sPerp,funext_iff]
  grind [sqrt_two_pow_sub_ne_zero n hn]

-- minus 1 eigenvalue
lemma diffusion_negates_perp (ω : Register n) : (diffusion n) • perp ω = -perp ω := by
  have hsum : ∑ k, (perp ω) k = 0 := by
    simp only [perp, Finset.sum_sub_distrib, Pi.sub_apply, Pi.smul_apply, ← Finset.smul_sum]
    simp [basisVector_def, sum_sPerp, sin_groverTheta_eq, cos_groverTheta_eq]
    grind [sqrt_two_pow_sub_sq n]
  simp [diffusion_reflection,hsum]


lemma oracle_coord (ω : Register n) (hω : f ω = 1) (hb : ∀ k, k ≠ ω → f k = 0)
  (v : EuclideanSpace ℝ (Fin 2)) :
    oracle f • coord ω v = coord ω (reflectTarget v) := by
  simp only [reflectTarget,funext_iff,coord, DistribSMul.smul_add, smul_comm,
    oracle_apply_omega f hω, oracle_apply_sPerp f ω hb]
  simp

-- eigenbasis {HH n • δ[0], perp ω}
-- δ[ω] and sPerp ω are rotated by an angle
lemma delta_in_eigenbasis (ω : Register n) (hn : n ≠ 0) :
  δ[ω] = (Real.sin (groverTheta n) : ℂ) • (HH n • δ[0]) + (Real.cos (groverTheta n) : ℂ) • perp ω
  := by
  rw [perp,uniform_decomp_orthonormal ω hn]
  match_scalars <;> norm_num <;> ring_nf
  simp

lemma sPerp_in_eigenbasis (ω : Register n) (hn : n ≠ 0) :
  sPerp ω = (Real.cos (groverTheta n) : ℂ) • (HH n • δ[0]) - (Real.sin (groverTheta n) : ℂ) • perp ω
  := by
  rw [perp,uniform_decomp_orthonormal ω hn]
  match_scalars <;> norm_num <;>ring_nf
  simp

lemma diffusion_eigen (ω : Register n) (a b : ℂ) :
  (diffusion n) • (a • (HH n • δ[0]) + b • perp ω) = a • (HH n • δ[0]) - b • perp ω
  := by
  rw [smul_add, smul_comm (diffusion n) a, smul_comm (diffusion n) b,
      diffusion_fixes_uniform, diffusion_negates_perp, smul_neg]
  grind

lemma diffusion_omega (ω : Register n) (hn : n ≠ 0) :
    (diffusion n) • δ[ω] = coord ω !₂[-Real.cos (2*groverTheta n), Real.sin (2*groverTheta n)] := by
  rw [delta_in_eigenbasis ω hn, diffusion_eigen ω _ _,perp,coord]
  norm_num [funext_iff, uniform_decomp_orthonormal ω hn,Real.cos_two_mul, Real.sin_two_mul]
  grind [Complex.sin_sq_add_cos_sq]

lemma diffusion_sPerp (ω : Register n) (hn : n ≠ 0) :
  (diffusion n) • sPerp ω = coord ω !₂[Real.sin (2*groverTheta n), Real.cos (2*groverTheta n)] := by
  rw [sPerp_in_eigenbasis ω hn, sub_eq_add_neg, ← neg_smul, diffusion_eigen ω _, neg_smul,perp]
  norm_num [funext_iff, uniform_decomp_orthonormal ω hn, coord,Real.cos_two_mul, Real.sin_two_mul]
  grind [Complex.sin_sq_add_cos_sq]

-- Diffusion is a reflection too
lemma diffusion_coord (ω : Register n) (hn : n ≠ 0)
  (v : EuclideanSpace ℝ (Fin 2)) : (diffusion n) • coord ω v =
    coord ω (groverOrientation.rotation (2 * groverTheta n : ℝ) (reflectTarget v)) := by
  ext
  simp [reflectTarget, Orientation.rotation_apply, groverOrientation_rightAngle, coord,
      smul_comm (diffusion n), diffusion_omega ω hn, diffusion_sPerp ω hn]
  ring

-- composing two reflections (diffusion and oracle) is a rotation by 2θ.
lemma groverIterate_coord (ω : Register n) (hn : n ≠ 0) (hω : f ω = 1)
    (hb : ∀ k, k ≠ ω → f k = 0) (v : EuclideanSpace ℝ (Fin 2)) :
    groverIterate f • coord ω v =
      coord ω (groverOrientation.rotation (2 * groverTheta n : ℝ) v) := by
  rw [groverIterate, SemigroupAction.mul_smul, oracle_coord f ω hω hb,diffusion_coord ω hn]
  with_reducible_and_instances congr 2
  matrix_expand [reflectTarget]

lemma grover_coord_rotation (ω : Register n) (hn : n ≠ 0)
    (hω : f ω = 1) (hb : ∀ k, k ≠ ω → f k = 0) (t : ℕ) :
  grover f t = coord ω (groverOrientation.rotation (2 * t * groverTheta n : ℝ)
      !₂[Real.sin (groverTheta n), Real.cos (groverTheta n)]) := by
  induction t with
  | zero =>
    simp [funext_iff,Orientation.rotation_zero,grover, uniform_decomp_orthonormal ω hn, coord]
  | succ t ih =>
    simp only [grover, pow_succ', SemigroupAction.mul_smul] at ih ⊢
    norm_num [ih, groverIterate_coord f ω hn hω hb, ← Real.Angle.coe_add]
    ring_nf

lemma grover_rotation (ω : Register n) (hn : n ≠ 0) (hω : f ω = 1)
  (hb : ∀ k, k ≠ ω → f k = 0) (t : ℕ) :
  grover f t = (Real.sin ((2 * t + 1) * groverTheta n) : ℂ) • δ[ω] +
    (Real.cos ((2 * t + 1) * groverTheta n) : ℂ) • sPerp ω := by
  norm_num [grover_coord_rotation f ω hn hω hb, groverOrientation_rotation_comp, coord]
  ring_nf

theorem grover_success_prob (ω : Register n) (hn : n ≠ 0)
    (hω : f ω = 1) (hb : ∀ k, k ≠ ω → f k = 0) (r : ℕ) :
    ‖(grover f r) ω‖^2 = Real.sin ((2 * r + 1) * groverTheta n) ^ 2 := by
  simp_rw [grover_rotation f ω hn hω hb,Pi.add_apply, Pi.smul_apply, smul_eq_mul,sPerp_apply,
  if_true,basisVector_def, Pi.basisFun_apply, Pi.single_eq_same,mul_zero, add_zero, mul_one,
  Complex.norm_real,Real.norm_eq_abs, sq_abs]

-- Finding per-iteration success probability of grover is the hard part and has been done.
-- Arguing about the best iteration r is simple but tedious algerba without much physics.
-- This is done below:

noncomputable def r_grover (n : ℕ) : ℕ := Nat.floor (π / (4 * groverTheta n))

lemma r_grover_window :
    |(2 * r_grover n + 1) * groverTheta n - π/2| ≤ groverTheta n := by
  have hpos : 0 < groverTheta n := groverTheta_pos
  have hpos2 : 0 ≤ π / (4 * groverTheta n) := by positivity
  have hpi : 2 * (π / (4 * groverTheta n)) * groverTheta n = π / 2 := by field_simp; ring
  rw [r_grover, abs_le]
  constructor <;>
  nlinarith [hpi, hpos.le, Nat.floor_le hpos2, Nat.lt_floor_add_one (π / (4 * groverTheta n))]

lemma sin_square_phi_gt {φ θ : ℝ}
    (hθ : 0 ≤ θ) (hθover4 : θ ≤ π / 4) (hw : |φ - π / 2| ≤ θ) : 1 - Real.sin φ ^ 2 ≤ Real.sin θ ^ 2
  := by
  have hge : Real.cos θ ≤ Real.sin φ := by
    rw [Eq.symm (Real.cos_sub_pi_div_two φ),← Real.cos_abs (φ - π/2)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hw
  have hcos_pos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨?_,?_ ⟩<;>
  nlinarith [Real.pi_pos, Real.sin_sq_add_cos_sq θ, Real.sin_sq_add_cos_sq φ]

theorem grover_finds_target (ω : Register n) (hn : n ≠ 0)
    (hω : f ω = 1) (hb : ∀ k, k ≠ ω → f k = 0) :
    1 - ‖(grover f (r_grover n)) ω‖ ^ 2 ≤ 1 / 2 ^ n := by
  rw [grover_success_prob f ω hn hω hb]
  have := sin_square_phi_gt groverTheta_pos.le (groverTheta_le hn) (r_grover_window)
  grind [sin_groverTheta_eq, amp_sq n]

lemma r_grover_upper_bound : r_grover n  ≤ π / 4 * Real.sqrt (2 ^ n) := by
  have hθ : 0 < groverTheta n := groverTheta_pos
  have: (√2)⁻¹ ^ n ≤ groverTheta n := sin_groverTheta_eq n ▸ (Real.sin_lt hθ).le
  refine (Nat.floor_le (by positivity)).trans ?_
  ring_nf
  with_reducible_and_instances gcongr
  rw [Real.le_sqrt' (by positivity), ← inv_inv (2 ^ n), ← one_div (2 ^ n), ← amp_sq n, ← inv_pow]
  with_reducible_and_instances gcongr

--- A final theorem that wraps up the important results

theorem grover_search (ω : Register n) (hn : n ≠ 0) (hω : f ω = 1) (hb : ∀ k, k ≠ ω → f k = 0) :
  ∃ r : ℕ, r  ≤ π / 4 * Real.sqrt (2 ^ n) ∧ 1 - ‖(grover f r) ω‖ ^ 2 ≤ 1 / 2 ^ n :=
  ⟨r_grover n, r_grover_upper_bound , grover_finds_target f ω hn hω hb⟩
