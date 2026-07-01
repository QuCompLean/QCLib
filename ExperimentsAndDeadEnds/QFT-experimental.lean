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
/-- Orthogonality of characters -/
theorem stdChar_orthogonal (N : ℕ) [NeZero N] (t s : ZMod N) :
    ∑ x, stdAddChar (t * x) * conj (stdAddChar (s * x)) = if t = s then ↑N else 0 := by
  simp [← inv_apply_eq_conj, ← inv_apply', ← map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, mul_comm,
    AddChar.sum_mulShift _ (isPrimitive_stdAddChar N), sub_eq_zero]

/-- A character of order `d ^ (n + 1)` evaluated at `x * d` equals the character
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

/-- The matrix representation of the inverse DFT for `ZMod N`, also known as the Schur matrix -/
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

/-- The inverse DFT for `ZMod N`, normalized and bundled as a unitary matrix
with index type `Fin N` -/
@[simps! -isSimp coe]
def UnitaryGroup.idftFin : 𝐔[Fin N] :=
  reindexMonoidEquiv (ZMod.finEquiv N).symm (idftZMod N)

@[simp]
theorem UnitaryGroup.idftFin_apply (a b) : idftFin N a b = √N⁻¹ • ζ N ^ (a * b : ℕ) := by
  simp [idftFin_coe, stdAddChar_apply, toCircle_apply, ← map_mul, ← div_mul_eq_mul_div,
    exp_nat_mul', show cexp (2 / N * ↑π * I) = ζ N by grind [ζ_def], ζ_pow_mul]

end idftZMod

public section QFT

variable (n d : ℕ) [d.AtLeastTwo]

/-- The QFT for `ZMod (d ^ n)`, normalized and bundled as a unitary matrix
with index type `Fin n → Fin d` -/
noncomputable def QFT : 𝐔[Fin n → Fin d] :=
  reindexMonoidEquiv digitsEquiv (UnitaryGroup.idftZMod (d ^ n))

@[simp]
theorem QFT_apply (k l : Fin n → Fin d) :
    QFT n d k l = √((d ^ n)⁻¹) • stdAddChar (k.ofDigits * l.ofDigits) := by
  simp [QFT]

/-- The QFT for `ZMod (d ^ n)`, normalized and bundled as a unitary matrix
with index type `Fin n → Fin d`, TB -/
noncomputable def QFTRev : 𝐔[Fin n → Fin d] :=
  (QFT n d) * ((permSubsystemsHom ℂ (Fin d)) Fin.revPerm)

@[simp]
theorem QFTRev_apply (k l : Fin n → Fin d) :
    QFTRev n d k l = √((d ^ n)⁻¹) • stdAddChar (k.ofDigits * l.ofDigitsBE) := by
  simp [QFTRev, ofDigitsBE_apply']

/- Theory of the "controlled-rotations" blocks in the QFT circuit -/
public noncomputable section CRCircuit

open Finset

variable {d n : ℕ} (k : ℕ)

/-- The diagonal gate which multiples `|x>` with `e^{i 2 π / d^k x}`, for `x : Fin d` -/
def R (k : ℕ) : 𝐔[Fin d] :=
  diagonalMonoidHom (fun x ↦ (uζ (d ^ k)) ^ (x : ℕ))

theorem CR_diagonal :
    controllize d (R k) =
      diagonalMonoidHom (fun x : Fin d × Fin d ↦ (uζ (d ^ k)) ^ (x.2 * x.1 : ℕ)) := by
  simp [R, controllize_diagonal, pow_mul]

theorem CR_at_diagonal (i j : Fin n) (hneq : i ≠ j) {d : ℕ} (k : ℕ) :
    bipartite i j (controllize d (R k)) hneq =
      diagonalMonoidHom (fun x : Fin n → Fin d ↦ uζ (d ^ k) ^ (x j * x i : ℕ)) := by
  simp [CR_diagonal, bipartite_diagonal]

/-- The block of the QFT that consists of controlled-`R` gates -/
def CRCircuit (d) (i : Fin n) : 𝐔[Fin n → Fin d] :=
  ((Ioi i).attach.toList.map
    (fun j : Ioi i ↦ bipartite j.val i (controllize d (R (j + 1 - i))))
  ).prod

theorem pow_uζ_eq_stdAddchar (x : ℕ) [NeZero d] :
    uζ (d ^ n) ^ x = stdAddChar (x.cast : ZMod (d ^ n)) := by
  rw [stdAddChar_apply, toCircle_apply, coe_uζ, ζ_def, ← Complex.exp_nat_mul']
  sorry

private lemma prod_uζ (d n : ℕ) (i : Fin n) (y : Fin n → Fin d) [hd : NeZero d] :
    ∏ j > i, (uζ (d ^ (j + 1 : ℕ))) ^ (d ^ (i : ℕ) * y i * y j) =
      (uζ (d ^ n)) ^ (∑ j > i, (d ^ (j.rev + i : ℕ) * y i * y j)) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  congr! 1 with j
  simp_rw [uζ_pow_fin_rev, ← pow_mul, ←mul_assoc, pow_add]

private theorem CRCircuit_eq (i : Fin n) [hd : NeZero d] :
    CRCircuit d i =
      diagonalMonoidHom fun y : Fin n → Fin d ↦
          (uζ (d ^ n)) ^ (∑ j > i, (d ^ (j.rev + i : ℕ) * y i * y j)) := by
  simp_rw [← prod_uζ (hd := hd), ← Finset.prod_attach (s := Ioi i), CRCircuit,
    CR_at_diagonal, ← prod_diagonal]
  congr! 1
  apply List.map_congr_left (fun a h ↦ ?_)
  congr! 2
  simp [pow_mul, ← uζ_pow_sub hd.out (by grind : i.val ≤ a + 1)]

private theorem CRCircuit_eq_reindexed (i : Fin n) [hd : NeZero d] :
    CRCircuit d i = diagonalMonoidHom fun y : Fin n → Fin d ↦
      (uζ (d ^ n)) ^ (∑ j < i.rev, (d ^ (j + i : ℕ) * y i * y j.rev)) := by
  rw [CRCircuit_eq]
  congr! 3 with x
  exact Finset.sum_equiv Fin.revPerm (by simp_all) (by simp)

end CRCircuit


variable [NeZero n]

theorem rec1 (k l : Fin (n + 1) → Fin d) :
  QFTRev (n + 1) d k l =
    (√(d⁻¹) • stdAddChar (∑ i, k i * l (Fin.last n) * (d ^ (i : ℕ)) : ZMod (d ^ (n + 1)))) *
      (QFTRev n d (Fin.init k) (Fin.init l)) := by
  rw [QFTRev_apply, idftRec]
  have : √((d ^ (n + 1))⁻¹) = √(d⁻¹) * √((d ^ n)⁻¹) := by
    rw [← Real.sqrt_mul (by positivity), ← mul_inv, mul_comm, pow_succ]
  rw [this]
  rw [← smul_eq_mul, smul_assoc, mul_comm, ← mul_smul_comm, ← QFTRev_apply, smul_mul_assoc]
-- ↑ just chained assoc and comm lemmas until it worked... :/

public noncomputable section QFTCircuit

open UnitaryGroup OuterProduct

/-- The circuit of the QFT, using big-endian order for the right index type, and
little-endian order for the left index type. -/
def QFTRevCircuit (n d : ℕ) [NeZero d] : 𝐔[Fin n → Fin d] := match n with
  | 0 => 1
  | n + 1 =>
    (single 0 (idftFin d)) * CRCircuit d 0 * (embedRight (QFTRevCircuit n d))

theorem xxx (n d : ℕ) [d.AtLeastTwo] [NeZero n] :
    QFTRev (n + 1) d = (single (Fin.last n) (idftFin d)) * CRCircuit d (Fin.last n) * (embedLeft (QFTRev n d)) := by
  ext k l
  rw [test2comm]
  rw [QFTRev_apply]
  rw [embedLeft_apply_apply]


theorem QFTRevCircuit_eq_QFTRev (n d : ℕ) [d.AtLeastTwo] : QFTRevCircuit n d = QFTRev n d := by
  induction n with
  | zero =>
    ext i j
    simp [QFTRevCircuit, Subsingleton.elim i j]
    erw [AddChar.map_zero_eq_one] -- TBD.
  | succ n ih =>
    rw [test2]


/-- The circuit of the QFT -/
def QFTCircuit (n d : ℕ) [NeZero d] := QFTRevCircuit n d * revCircuit (Fin d) n

set_option linter.flexible false in
theorem QFTCircuit_eq_QFT (n d : ℕ) [d.AtLeastTwo] : QFTCircuit n d = QFT n d := by
  rw [← mul_left_inj (revCircuit (Fin d) n), QFTCircuit,
    mul_assoc, revCircuit_involution, mul_one, revCircuit_eq_revPermSubsystems]
  induction n with
  | zero =>
    ext i j
    simp [QFTRevCircuit, Subsingleton.elim i j]
    erw [AddChar.map_zero_eq_one] -- TBD.
  | succ n ih =>
    rw [test2]


-- theorem QFTRev_apply' (k l : Fin n → Fin d) :
--     QFTRev n d k l = QFT n d k (l ∘ Fin.revPerm) := by
--   simp [QFTRev, QFT]
