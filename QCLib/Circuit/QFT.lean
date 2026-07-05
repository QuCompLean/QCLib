/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Davood Tehrani, David Gross
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import QCLib.Circuit.Permutation
public import QCLib.Data.Fin.Digits

/-!

# Quantum Fourier transform for `ℤ_{d ^ n}`.

A *quantum Fourier transform* is a discrete Fourier transform interpreted as a
unitary map on a Hilbert space associated with a quantum system.

For such a unitary to be physically meaningful, it needs to have an efficient
gate decomposition.

In this file, we define a gate decomposition for the discrete Fourier transform
on `ℤ_{d ^ n}`.

The definitions follow the (somewhat unfortunate) convention used in https://en.wikipedia.org/wiki/Quantum_Fourier_transform.
In particular, the normalized DFT matrix is taken to have elements

 `DFT k l = √(N⁻¹) • stdAddChar (- k * l) = √(N⁻¹) • e^{- i 2 π / (d ^ n) k l}`

whereas the unitary representating the QFT has elements

 `QFT k l = √(N⁻¹) • stdAddChar (k * l) = √(N⁻¹) • e^{i 2 π / (d ^ n) k l}`,

which is the inverse (or the element-wise conjugate) of the DFT matrix.

## Main  definitions

- `QFCircuit n d` The circuit of the quantum Fourier transform for `ℤ_{d ^ n}`

## Main results

- `QFTCircuit_eq_QFT` The unitary resulting from the circuit equals the quantum
Fourier transform

## Implementation notes

By convention, the QFT uses big-endian order for representing elements of `ZMod d ^ n`
in terms of tuples `Fin n → Fin d`.

However, it is well-known that a version of the QFT using big-endian order for
the right index type, and little-endian order for the left index type leads to a
cleaner, recursive structure of the circuit. See e.g. https://arxiv.org/abs/quant-ph/0411069.

As an intermediate step, we thus define `QFTRevCircuit`, which implements a
circuit for this mixed convention.


## To do

- While the circuit decomposition we provide is easily seen to have complexity
quadratic in `n`, we have not yet formalized the scaling behavior.

- This file introduces many versions of the DFT, with slightly different
normalizations and index types. Maybe this can be reduced.

- We're mixing Mathlib's `stdAddChar` with our own `RootsOfUnity` definitions.
Maybe settle on one?

- TBD: This is a first implementation. Lots of clean-up potential. In
particular, one should probably rephrase the circuit using `embedLeft`, so that
the recursive structure is easier to exploit.

-/


open Matrix UnitaryGroup PiOuterProduct ComplexConjugate Fin


public section Aux

open ZMod

@[simp]
theorem finEquiv_val {n} [NeZero n] (a : Fin n) :
    (finEquiv n a).val = ↑a := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ n => rfl

open AddChar in
theorem stdChar_orthogonal (N : ℕ) [NeZero N] (t s : ZMod N) :
    ∑ x, stdAddChar (t * x) * conj (stdAddChar (s * x)) = if t = s then ↑N else 0 := by
  simp [← inv_apply_eq_conj, ← inv_apply', ← map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, mul_comm,
    sum_mulShift _ (isPrimitive_stdAddChar N), sub_eq_zero]

variable {n d : ℕ} [hd : NeZero d]

open Function

private theorem ζ_aux (x : Fin n → Fin d) (u : Fin (d ^ n)) :
   (∏ i : Fin n, ζ (d ^ (i + 1 : ℕ)) ^ (u * (x i) : ℕ)) =  ζ (d ^ n) ^ (u * ofDigitsBE x : ℕ) := by
  rw [val_ofDigitsBE_apply_reindex]
  simp [ζ_pow_fin_rev, ← pow_mul, Finset.prod_pow_eq_pow_sum, ← mul_assoc, mul_comm, Finset.mul_sum]
  lia

private lemma prod_uζ (d n : ℕ) (i : Fin n) (y : Fin n → Fin d) [hd : NeZero d] :
    ∏ j > i, (uζ (d ^ (j + 1 : ℕ))) ^ (d ^ (i : ℕ) * y i * y j) =
      (uζ (d ^ n)) ^ (∑ j > i, (d ^ (j.rev + i : ℕ) * y i * y j)) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  congr! 1 with j
  simp_rw [uζ_pow_fin_rev, ← pow_mul, ←mul_assoc, pow_add]

private theorem ζ_ofDigitsBE_ofDigits (f g : Fin (n + 1) → Fin d) :
    ζ (d ^ (n + 1)) ^ ((f.ofDigitsBE : ℕ) * g.ofDigits)
      = ζ (d ^ (n + 1)) ^ (
          (ofDigitsBE (tail f) : ℕ) * g 0
          + f 0 * g 0 * d ^ n
          + (tail f).ofDigitsBE * (tail g).ofDigits * d ) := by
  simp [ofDigitsBE_ofDigits_rec, ζ_pow_eq_pow_iff_modEq]

private lemma cons_iff {n d} (a x v : Fin (n + 1) → Fin d) :
    ((∀ (k : Fin (n + 1)), ¬k = 0 → x k = a k) ∧ x 0 = v 0) ↔
      x = Fin.cons (v 0) (fun i : Fin n => a i.succ) := by
  constructor
  · rintro ⟨h, h0⟩
    funext k
    rcases k.eq_zero_or_eq_succ with rfl | ⟨i, rfl⟩ <;> simp_all
  · rintro rfl
    refine ⟨fun k hk => ?_, by simp⟩
    rcases k.eq_zero_or_eq_succ with rfl | ⟨i, rfl⟩ <;> simp_all

end Aux


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

/-- The inverse DFT for `ZMod N`, normalized and bundled as a unitary matrix
with index type `Fin N` -/
@[simps! -isSimp coe]
def UnitaryGroup.idftFin : 𝐔[Fin N] :=
  reindexMonoidEquiv (ZMod.finEquiv N).symm (idftZMod N)

@[simp]
theorem UnitaryGroup.idftFin_apply (a b) : idftFin N a b = √N⁻¹ • ζ N ^ (a * b : ℕ) := by
  simp [idftFin_coe, stdAddChar_apply, toCircle_apply, ← map_mul, ← div_mul_eq_mul_div,
    exp_nat_mul', show cexp (2 / N * ↑π * I) = ζ N by grind [ζ_def], ζ_pow_mul]

theorem UnitaryGroup.idftFin_apply_basis (v : Fin N) :
    idftFin N • δ[v] = ∑ k : Fin N, (√N⁻¹ * ζ N ^ (k * v : ℕ)) • δ[k] := by
  ext
  simp [basisVector_def, Submonoid.smul_def, Pi.single_apply]

/-- The DFT for `ZMod N`, normalized and bundled as a unitary matrix with index type `Fin N` -/
def UnitaryGroup.dftFin : 𝐔[Fin N] := star (idftFin N)

@[simp]
theorem UnitaryGroup.dftFin_apply (a b) : dftFin N a b = √N⁻¹ • conj (ζ N ^ (a * b : ℕ)) := by
  simp [dftFin, mul_comm]

@[simp]
theorem UnitaryGroup.dftFin_apply_basis (v : Fin N) :
    dftFin N • δ[v] = ∑ k : Fin N, (√N⁻¹ * conj (ζ N ^ (k * v : ℕ))) • δ[k] := by
  ext
  simp [basisVector_def, Submonoid.smul_def, Pi.single_apply]

end idftZMod

public section QFT

variable (n d : ℕ) [hdz : NeZero d]

/-- The QFT for `ZMod (d ^ n)`, normalized and bundled as a unitary matrix
with index type `Fin n → Fin d` -/
noncomputable def QFT : 𝐔[Fin n → Fin d] :=
  reindexMonoidEquiv Function.ofDigitsBE.symm (UnitaryGroup.idftFin (d ^ n))

@[simp] theorem QFT_apply (a b) :
    QFT n d a b = √(d ^ n)⁻¹ * (ζ (d ^ n)) ^ (a.ofDigitsBE * b.ofDigitsBE : ℕ) := by
  simp [QFT]

theorem QFT_apply_basis (v : Fin n → Fin d) :
    QFT n d • δ[v] =
      ∑ k, (√(d ^ n)⁻¹ * (ζ (d ^ n)) ^ (v.ofDigitsBE * k.ofDigitsBE : ℕ)) • δ[k] := by
  simp [apply_basis, mul_comm]

theorem QFT_apply_basis_eq_tprod (v : Fin n → Fin d) :
    QFT n d • δ[v] = ⨂ i : Fin n,
      (√d⁻¹ : ℂ) • ∑ j : Fin d, ζ (d ^ (i + 1 : ℕ)) ^ (v.ofDigitsBE * j : ℕ) • δ[j] := by
  simp_rw [piOuterProduct_smul_univ, QFT_apply_basis, basisVector_eq_prod, ← smul_eq_mul,
    smul_assoc]
  simp [← Finset.smul_sum, ← ζ_aux, ← piOuterProduct_smul_univ, piOuterProduct_univ_sum,
    Real.sqrt_pow]

end QFT

/- Theory of the "controlled-rotations" blocks in the QFT circuit -/
public noncomputable section CRCircuit

open Finset

variable {d n : ℕ} (k : ℕ)

/-- The diagonal gate which multiplies `|x>` with `e^{i 2 π / d^k x}`, for `x : Fin d` -/
def R : 𝐔[Fin d] :=
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
  ((Ioi i).attach.toList.map (
    fun j : ↥(Ioi i) ↦ bipartite j.val i (controllize d (R (j + 1 - i)))
  )).prod

private theorem CRCircuit_eq (i : Fin n) [hd : NeZero d] :
    CRCircuit d i =
      diagonalMonoidHom fun y : Fin n → Fin d ↦
          (uζ (d ^ n)) ^ (∑ j ∈ Finset.Ioi i, (d ^ (j.rev + i : ℕ) * y i * y j)) := by
  simp_rw [← prod_uζ (hd := hd), ← Finset.prod_attach (s := Ioi i), CRCircuit,
    CR_at_diagonal, ← prod_diagonal]
  congr! 1
  apply List.map_congr_left (fun a h ↦ ?_)
  congr! 2
  simp [pow_mul, ← uζ_pow_sub hd.out (by grind : i.val ≤ a + 1)]

private theorem CRCircuit_eq_reindexed (i : Fin n) [hd : NeZero d] :
    CRCircuit d i = diagonalMonoidHom fun y : Fin n → Fin d ↦
      (uζ (d ^ n)) ^ (∑ j ∈ Finset.Iio i.rev, (d ^ (j + i : ℕ) * y i * y j.rev)) := by
  rw [CRCircuit_eq]
  congr! 3 with x
  exact Finset.sum_equiv Fin.revPerm (by simp_all) (by simp)

end CRCircuit


public noncomputable section QFTCircuit

open UnitaryGroup OuterProduct

-- The definition allows for `n = 0` or `d = 1`. These cases aren't of physical interest.
/-- The circuit of the QFT, using big-endian order for the right index type, and
little-endian order for the left index type. -/
def QFTRevCircuit (n d : ℕ) [NeZero d] : 𝐔[Fin n → Fin d] := match n with
  | 0 => 1
  | n + 1 =>
    (single 0 (idftFin d)) * CRCircuit d 0 * (embedRight (QFTRevCircuit n d))

/-- The circuit of the QFT -/
def QFTCircuit (n d : ℕ) [NeZero d] := QFTRevCircuit n d * revCircuit (Fin d) n

set_option linter.flexible false in
/-- The circuit realizes the QFT.

TBD: Break the proof into smaller, less fragile pieces -/
theorem QFTCircuit_eq_QFT (n d : ℕ) [hd : NeZero d] : QFTCircuit n d = QFT n d := by
  rw [← mul_left_inj (revCircuit (Fin d) n), QFTCircuit,
    mul_assoc, revCircuit_involution, mul_one, revCircuit_eq_revPermSubsystems]
  induction n with
  | zero =>
    ext i j
    simp [QFTRevCircuit, Subsingleton.elim i j]
  | succ n ih =>
    apply ext_smul_basis
    intro v
    simp_rw [QFTRevCircuit, ih, ← smul_eq_mul, smul_assoc, embedRight_apply_basis]
    ext a
    -- Application on basis
    simp [Function.comp_def, -permSubsystemsHom_smul_basis, CRCircuit_eq_reindexed]
    simp [basisVector_def, Submonoid.smul_def, mulVec_eq_sum, blockDiagonal_apply, funext_iff]
    simp [Pi.single_apply, ← ite_and, cons_iff, ζ_ofDigitsBE_ofDigits]
    -- Normalization
    field_simp
    simp [show (√d * √(d ^ n)) = (√(d ^ (n + 1)) : ℂ) by simp [pow_succ'],
      div_left_inj' (show (√(d ^ (n + 1)) : ℂ) ≠ 0 by simp [hd.out])]
    -- Elementary math
    simp [← ζ_pow_succ d n, ← ζ_pow_succ' d n, ← pow_mul, ← pow_add,
      val_ofDigitsBE_apply, tail, Function.ofDigits_apply, Fin.rev_castSucc]
    nth_rw 2 [Finset.sum_mul]
    grind


public section IQFT

variable (n d : ℕ) [hdz : NeZero d]

noncomputable def IQFT : 𝐔[Fin n → Fin d] := (QFT n d)⁻¹

@[simp] theorem IQFT_apply (a b) :
    IQFT n d a b = √(d ^ n)⁻¹ * conj ((ζ (d ^ n)) ^ (a.ofDigitsBE * b.ofDigitsBE : ℕ)) := by
  simp [IQFT, mul_comm]

theorem IQFT_apply_basis (v : Fin n → Fin d) :
    IQFT n d • δ[v] =
      ∑ k, (√(d ^ n)⁻¹ * conj ((ζ (d ^ n)) ^ (v.ofDigitsBE * k.ofDigitsBE : ℕ))) • δ[k] := by
  simp [apply_basis, mul_comm]

theorem IQFT_apply_basis_eq_tprod (v : Fin n → Fin d) :
    IQFT n d • δ[v] = ⨂ i : Fin n,
      (√d⁻¹ : ℂ) • ∑ j : Fin d, conj ζ (d ^ (i + 1 : ℕ)) ^ (v.ofDigitsBE * j : ℕ) • δ[j] := by
  simp_rw [piOuterProduct_smul_univ, IQFT_apply_basis, basisVector_eq_prod, ← smul_eq_mul,
    smul_assoc]
  simp [← Finset.smul_sum, ← ζ_aux, ← piOuterProduct_smul_univ, piOuterProduct_univ_sum,
    Real.sqrt_pow]

end IQFT
