/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import QCLib.Data.ZMod.Digits
public import QCLib.Circuit.Permutation
public import QCLib.LinearAlgebra.UnitaryGroup.RootsOfUnity

/-
# Experiments
-/

open Matrix UnitaryGroup PiOuterProduct ComplexConjugate

public section equivFin

public section Aux

open ZMod

open AddChar in
theorem stdChar_orthogonal (N : ℕ) [NeZero N] (t s : ZMod N) :
    ∑ x, stdAddChar (t * x) * conj (stdAddChar (s * x)) = if t = s then ↑N else 0 := by
  simp [← inv_apply_eq_conj, ← inv_apply', ← map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, mul_comm,
    AddChar.sum_mulShift _ (isPrimitive_stdAddChar N), sub_eq_zero]
-- This should go into QFT.lean

/-- A character of order `d ^ n.succ` evaluated at `x * d` equals the character
of order `d ^ n` evaluated at x. -/
theorem stdAddChar_mul_cast_succ {d n : ℕ} [NeZero d] (x : ZMod (d ^ n)) :
    stdAddChar (x.cast * d : ZMod (d ^ (n + 1))) = stdAddChar x := by
  conv_rhs => rw [← natCast_zmod_val x]
  simp_rw [cast_eq_val, ← Nat.cast_mul, stdAddChar_apply, toCircle_natCast, pow_add]
  push_cast
  field_simp [NeZero.ne _]

/-- A recursive formula for the inverse DFT matrix. Note that the first
`stdAddChar` on the rhs is of order `d ^ n`, while the other characters have
order `d ^ (n + 1)`. -/
theorem idftRec {n d : ℕ} [d.AtLeastTwo] [NeZero n] (k x : Fin (n + 1) → Fin d) :
  stdAddChar (k.ofDigits * x.ofDigitsBE) =
    stdAddChar ((Fin.init k).ofDigits * (Fin.init x).ofDigitsBE) *
      stdAddChar (∑ i, k i * x (Fin.last n) * (d ^ (i : ℕ)) : ZMod (d ^ (n + 1))) := by
  rw [ofDigits_mul_ofDigitsBE_rec, AddChar.map_add_eq_mul, stdAddChar_mul_cast_succ]

public noncomputable section idftZMod

open ZMod Complex Real

variable (N : ℕ) [NeZero N]

/-- The matrix representation of the inverse DFT for `ZMod N`, also known as the *Schur matrix* -/
def Matrix.idftZMod : Matrix (ZMod N) (ZMod N) ℂ :=
  of fun i j ↦ conj ((dft (Pi.single j 1)) i)

@[simp]
theorem Matrix.idftZMod_apply_apply (i j : ZMod N) : idftZMod N i j = stdAddChar (i * j) := by
  simp [idftZMod, ← AddChar.map_neg_eq_conj, dft_apply, Pi.single_apply, mul_comm]

/-- The inverse DFT for `ZMod N`, normalized and bundled as a unitary matrix
with index type `ZMod N` -/
@[simps coe, expose]
def UnitaryGroup.idftZMod : 𝐔[ZMod N] := ⟨√(N⁻¹) • Matrix.idftZMod N, by
  simp only [Real.sqrt_inv, mem_unitaryGroup_iff, star_smul, star_trivial, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, smul_assoc_symm, smul_eq_mul,
    show (√↑N)⁻¹ * (√↑N)⁻¹ = (N : ℝ)⁻¹ by grind]
  ext
  simp [Matrix.mul_apply, Matrix.one_apply, stdChar_orthogonal] ⟩

end idftZMod

public section QFT

variable (n d : ℕ) [d.AtLeastTwo]

/-- The QFT for `ZMod (d ^ n)`, normalized and bundled as a unitary matrix
with index type `Fin n → Fin d` -/
noncomputable def QFT : 𝐔[Fin n → Fin d] :=
  reindexMonoidEquiv digitsEquiv (UnitaryGroup.idftZMod (d ^ n))

/-- The QFT for `ZMod (d ^ n)`, normalized and bundled as a unitary matrix
with index type `Fin n → Fin d`, TB -/
noncomputable def QFTRev : 𝐔[Fin n → Fin d] :=
  (QFT n d) * ((permSubsystemsHom ℂ (Fin d)) Fin.revPerm)

theorem QFTRev_apply (k l : Fin n → Fin d) :
    QFTRev n d k l = √((d ^ n)⁻¹) • stdAddChar (k.ofDigits * l.ofDigitsBE) := by
  simp [QFTRev, QFT, ofDigitsBE_apply']

variable [NeZero n]

theorem test1 (k l : Fin (n + 1) → Fin d) :
  QFTRev (n + 1) d k l = √((d ^ (n + 1))⁻¹) •
    (stdAddChar ((Fin.init k).ofDigits * (Fin.init l).ofDigitsBE) *
      stdAddChar (∑ i, k i * l (Fin.last n) * (d ^ (i : ℕ)) : ZMod (d ^ (n + 1)))) := by
  rw [QFTRev_apply, idftRec]

theorem test2 (k l : Fin (n + 1) → Fin d) :
  QFTRev (n + 1) d k l = √(d⁻¹) •
    (QFTRev n d (Fin.init k) (Fin.init l)) *
      stdAddChar (∑ i, k i * l (Fin.last n) * (d ^ (i : ℕ)) : ZMod (d ^ (n + 1))) := by
  rw [QFTRev_apply, idftRec]
  have : √((d ^ (n + 1))⁻¹) = √(d⁻¹) * √((d ^ n)⁻¹) := by
    rw [← Real.sqrt_mul (by positivity), ← mul_inv, mul_comm, pow_succ]
  rw [this]
  rw [← smul_eq_mul, smul_assoc, mul_comm, ← mul_smul_comm, ← QFTRev_apply, mul_comm, smul_mul_assoc]
-- ↑ just chained assoc and comm lemmas until it worked... :/



-- theorem QFTRev_apply' (k l : Fin n → Fin d) :
--     QFTRev n d k l = QFT n d k (l ∘ Fin.revPerm) := by
--   simp [QFTRev, QFT]
