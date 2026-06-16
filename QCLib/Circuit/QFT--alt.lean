module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Fourier.ZMod
public import QCLib.Circuit.Permutation
public import QCLib.Circuit.Gate.Qubit
public import QCLib.Circuit.Embed

/-!
# QFT

-/

section Schur

namespace Matrix

variable {N : ℕ} [NeZero N]

open scoped ComplexConjugate

section ZMod

open ZMod

-- Is this in Mathlib?
open AddChar in
theorem stdChar_orthogonal (t s : ZMod N) :
    ∑ x, stdAddChar (t * x) * conj (stdAddChar (s * x)) = if t = s then ↑N else 0 := by
  have (x : ZMod N) : t * x + -(s * x) = x * (t - s) := by ring
  simp [← map_neg_eq_conj, ← map_add_eq_mul, this, sum_mulShift (t - s) (isPrimitive_stdAddChar N)]
  grind

variable (N)

/-- The matrix representation of the inverse DFT for `ZMod N`, also known as the *Schur matrix* -/
noncomputable def dftZMod : Matrix (ZMod N) (ZMod N) ℂ :=
  of fun i j ↦ conj ((dft (Pi.single j 1)) i)

@[simp]
theorem dftZMod_apply_apply (i j : ZMod N) : dftZMod N i j = stdAddChar (i * j) := by
  simp [dftZMod , ← AddChar.map_neg_eq_conj, dft_apply, Pi.single_apply, mul_comm]

@[simp]
theorem toCicle_one : toCircle (N := 1) = 1 := by
  ext x
  fin_cases x
  simp [toCircle_apply]

@[simp]
theorem dftZMod_one : dftZMod 1 = 1 := by
  ext i j
  simp [Matrix.one_apply, stdAddChar_apply, Subsingleton.elim i j]

namespace UnitaryGroup

-- TBD: Disproportionate effort is spent on the normalization factor...
/-- The matrix representation of the DFT for `ZMod N`, normalized and bundled as a unitary matrix -/
noncomputable def dftZMod : 𝐔[ZMod N] := ⟨√(N⁻¹) • _root_.Matrix.dftZMod N, by
    simp only [Real.sqrt_inv, mem_unitaryGroup_iff, star_smul, star_trivial, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_assoc_symm, smul_eq_mul,
      show (√↑N)⁻¹ * (√↑N)⁻¹ = (N : ℝ)⁻¹ by grind]
    ext
    simp [Matrix.mul_apply, Matrix.one_apply, stdChar_orthogonal] ⟩

@[simp, norm_cast]
theorem dftZMod_coe : (dftZMod N : Matrix (ZMod N) (ZMod N) ℂ) = √(N⁻¹) • _root_.Matrix.dftZMod N :=
  rfl

end ZMod.UnitaryGroup

namespace UnitaryGroup

variable (N)

/-- The matrix representation of the DFT for `Fin N`, normalized and bundled as a unitary matrix -/
@[simps!]
noncomputable def dftFin : 𝐔[Fin N] := reindexMonoidEquiv (ZMod.finEquiv N).symm (dftZMod N)

open Fin ComplexConjugate PiOuterProduct Qubit Matrix

-- TBD: move to `_root_.Fin.` namespace
@[simps! apply]
def equivFin {n d : ℕ} : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (arrowCongrLeftHom (Fin d) Fin.revPerm).trans finFunctionFinEquiv

theorem equivFin_apply' {n d} (f : Fin n → Fin d) :
    equivFin f = ∑ i : Fin n, (f i : ZMod (d ^ n)) * d ^ (i.rev : ℕ) := by
  simp_rw [equivFin_apply, finFunctionFinEquiv_apply_val]
  push_cast
  apply Finset.sum_equiv Fin.revPerm (by simp) (fun i hi ↦ ?_)
  simp

theorem finFunctionFinEquiv_mul_equivFin {n d} (k x : Fin n → Fin d) :
    (finFunctionFinEquiv k) * (equivFin x) =
      ∑ i : Fin n, ∑ j : Fin n, (k i : ZMod (d ^ n)) * (x j) * d ^ (i + j.rev : ℕ) := by
  simp only [equivFin_apply', finFunctionFinEquiv_apply_val] -- _3 also works??
  push_cast
  simp only [Fintype.sum_mul_sum]
  grind

-- maybe give up and let `d` be cast to `ZMod` already
private theorem aux2 {n d} [NeZero d] (j : Fin n) (k x : Fin n → Fin d) :
    ∑ i ∈ (Finset.Ioi j), (k i : ZMod (d ^ n)) * (x j) * (d ^ (i + (j.rev : ℕ))) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [ZMod.natCast_pow_eq_zero_of_le d] <;> grind

private theorem aux3 {n d} [NeZero d] (j : Fin n) (k x : Fin n → Fin d) :
    ∑ i : Fin n, (k i : ZMod (d ^ n)) * (x j) * (d ^ (i + (j.rev : ℕ))) =
      ∑ i ≤ j, (k i : ZMod (d ^ n)) * (x j) * (d ^ (i + (j.rev : ℕ))) :=  by
  have hu : Finset.univ = (Finset.Iic j) ∪ (Finset.Ioi j) := by grind
  have hd : Disjoint (Finset.Iic j) (Finset.Ioi j) := by grind [Finset.disjoint_left]
  rw [hu, Finset.sum_union hd, aux2, add_zero]

theorem char_finFunctionFinEquiv_mul_equivFin {n d} [NeZero d] (k x : Fin n → Fin d) :
    ZMod.stdAddChar ((finFunctionFinEquiv k * equivFin x) : ZMod (d ^ n)) =
      ZMod.stdAddChar (∑ j, ∑ i ≤ j, (k i) * (x j) * (d ^ (i + (j.rev : ℕ))) : ZMod (d ^ n)) := by
  rw [finFunctionFinEquiv_mul_equivFin, Finset.sum_comm]
  simp_rw [aux3]

-- lemma sum_register_univ_eq {n d} {M : Type*} [AddCommMonoid M] (f : (Fin n → Fin d) → M) :
--     ∑ r : Fin n → Fin d, f r = ∑ i, f (equivFin.symm i) :=
--   Finset.sum_equiv equivFin (by simp) (by simp)

/-- The quantum Fourier transform. -/
@[simps!]
noncomputable def QFT (d n : ℕ) [NeZero d] : 𝐔[Fin n → Fin d] :=
  reindexMonoidEquiv equivFin.symm (dftFin (d ^ n))

open ZMod

theorem QFT_apply {n d} [NeZero d] (a b : Fin n → Fin d) :
    QFT d n a b = √(d^n)⁻¹ * stdAddChar (finEquiv (d ^ n) (equivFin a * equivFin b)) := by
  simp

theorem QFT_apply_2 {n d} [NeZero d] (a b : Fin n → Fin d) :
    QFT d n a b =
      √(d^n)⁻¹ * (ζ (d ^ n)) ^ ((finEquiv (d ^ n) (equivFin a * equivFin b)).val) := by
  simp only [QFT_apply, ζ_def, stdAddChar_apply, toCircle_apply, ← Complex.exp_nsmul']
  ring_nf

theorem QFT_apply_3 {n d} [NeZero d] (a b : Fin n → Fin d) :
    QFT d n a b =
      √(d^n)⁻¹ * (ζ (d ^ n)) ^ ((finEquiv (d ^ n) (equivFin a * equivFin b)).val) := by
  simp only [QFT_apply, ζ_def]
  simp only [stdAddChar_apply, toCircle_apply, ← Complex.exp_nsmul']
  ring_nf

theorem thm0 {n d} [NeZero d] (a : Fin n → Fin d) :
    (finEquiv (d ^ n) (equivFin a)).val = ↑(equivFin a) := by
  apply?

  sorry
theorem thm1 {n d} [NeZero d] (a b : Fin n → Fin d) :
    (finEquiv (d ^ n) (equivFin a * equivFin b)).val = ↑(equivFin a * equivFin b) := by
  simp

  sorry

/-- The quantum Fourier transform, with output register least significant bit first. -/
@[simps!]
noncomputable def QFTRev (d n : ℕ) [NeZero d] : 𝐔[Fin n → Fin d] :=
   (permSubsystemsHom ℂ (Fin d) Fin.revPerm⁻¹) * (QFT d n)

-- TBD: Make proof nicer
theorem QFTRev_apply {n d} [NeZero d] (a b : Fin n → Fin d) :
    QFTRev d n a b = √(d^n)⁻¹ *
      stdAddChar (ZMod.finEquiv (d ^ n) (finFunctionFinEquiv a * equivFin b)) := by
  rw [QFTRev, permSubsystemsHom_eq_permHom, perm_mul_unitary_apply_apply, QFT_apply]
  with_reducible congr 4 -- oof.
  aesop

section dAdicRotations

noncomputable def R {d : ℕ} (k : ℕ) : 𝐔[Fin d] :=
  diagonalMonoidHom (fun x ↦ (uζ (d ^ k)) ^ (x : ℕ))

theorem CR_diagonal {d : ℕ} (k : ℕ) :
    controllize d (R k) =
      diagonalMonoidHom (fun x : Fin d × Fin d ↦ (uζ (d ^ k)) ^ (x.2 * x.1 : ℕ)) := by
  simp [R, controllize_diagonal, pow_mul]

theorem CR_at_diagonal {n : ℕ} {i j : Fin n} (hneq : i ≠ j) {d : ℕ} (k : ℕ) :
    bipartite i j (controllize d (R k)) hneq =
      diagonalMonoidHom (fun x : Fin n → Fin d ↦ (uζ (d ^ k)) ^ (x j * x i : ℕ)) := by
  simp [CR_diagonal, bipartite_diagonal]

end dAdicRotations

/-- The main diagonal of ...TBD... -/
noncomputable def CRAtFun {n : ℕ} (d : ℕ) (k : ℕ) (i j : Fin n) :
    (Fin n → Fin d) → unitary ℂ := fun x ↦ (uζ (d ^ k)) ^ (x j * x i : ℕ)

@[simp]
theorem CRAtFun_def {n : ℕ} (d : ℕ) [NeZero d] (k : ℕ) (i j : Fin n) :
  CRAtFun d k i j = fun x ↦ (uζ (d ^ k)) ^ (x j * x i : ℕ) := rfl

example {n : ℕ} (d : ℕ) [NeZero d] (x : Fin n.succ → Fin d) :
  (uζ (d ^ n)) ^ ((∑ i ∈ (Finset.Ioi (Fin.last n)), d ^ (i : ℕ) * (x i) * (x (Fin.last n))) : ℕ) =
    ∏ i ∈ (Finset.Ioi (Fin.last n)), (uζ (d ^ n)) ^ ((d ^ (i : ℕ) * (x i) * (x (Fin.last n))) : ℕ)
    := by
  rw [← Finset.prod_pow_eq_pow_sum]

example {n : ℕ} (d : ℕ) [NeZero d] (x : Fin n.succ → Fin d) :
  (uζ (d ^ n)) ^ ((∑ i ∈ (Finset.Ioi (Fin.last n)).attach, d ^ (i : ℕ) * (x i) * (x (Fin.last n))) : ℕ) =
    ∏ i ∈ (Finset.Ioi (Fin.last n)).attach, (uζ (d ^ n)) ^ ((d ^ (i : ℕ) * (x i) * (x (Fin.last n))) : ℕ)
    := by
  rw [← Finset.prod_pow_eq_pow_sum]

theorem t1 {n : ℕ} (d : ℕ) (hd : d ≠ 0) (x : Fin n.succ → Fin d) :
  (uζ (d ^ n)) ^ ((∑ i ∈ (Finset.Ioi (Fin.last n)).attach, d ^ (i : ℕ) * (x i) * (x (Fin.last n))) : ℕ) =
    ∏ i ∈ (Finset.Ioi (Fin.last n)).attach, (uζ (d ^ (n - i))) ^ (((x i) * (x (Fin.last n))) : ℕ)
    := by
  rw [← Finset.prod_pow_eq_pow_sum]
  congr
  ext i
  have : i ≤ n := by grind
  simp [uζ_pow_sub hd this, pow_mul]

noncomputable def CRCircuit {n : ℕ} (d : ℕ) : 𝐔[Fin (n+1) → Fin d] :=
  ((Finset.Ioi (Fin.last n)).attach.toList.map
    fun i ↦ bipartite i.val (Fin.last n) (controllize d (R (n - i.val))) (by grind)).prod

#check Finset.prod_eq_multiset_prod

theorem t2 {n : ℕ} (d : ℕ) (hd : d ≠ 0) :
    CRCircuit d =
      diagonalMonoidHom fun x : Fin n.succ → Fin d ↦
        (uζ (d ^ n)) ^ ((∑ i ∈ (Finset.Ioi (Fin.last n)).attach, d ^ (i : ℕ) * (x i) * (x (Fin.last n))) : ℕ) := by
  unfold CRCircuit
  simp_rw [CR_at_diagonal]
  simp_rw [t1 d hd]
  simp_rw [← Finset.prod_map_toList]
  simp only [← Function.comp_def]
  erw [List.prod_map_hom]
  simp only [Function.comp_def]
  congr
  ext1 x
  simp only [Finset.mem_Ioi, List.map_subtype, Pi.list_prod_apply, List.map_map]
  congr
  ext f
  simp [mul_comm]

noncomputable def QFTRevCircuit (d n : ℕ) [NeZero d] : 𝐔[Fin n → Fin d] :=
  match n with
    | 0 => 1
    | (n+1) =>
      (single (Fin.last n) (dftFin d)) * (CRCircuit d) * (succ (QFTRevCircuit d n))

@[simp]
theorem Fin.rev_zero : Fin.revPerm (n := 0) = 1 := by
  ext x
  fin_cases x

/-
  (star (Equiv.Perm.permMatrix ℂ (Equiv.arrowCongr 1 (Equiv.refl (Fin d)))⁻¹) *
      (1 • 1).submatrix (⇑(finEquiv 1) ∘ ⇑equivFin) (⇑(finEquiv 1) ∘ ⇑equivFin))
    j j

-/

#check Fin.elim0

theorem qft (d n : ℕ) [NeZero d] : (QFTRevCircuit d n) = QFTRev d n := by
  induction n with
  | zero =>
    ext i j
    simp [QFTRevCircuit, Subsingleton.elim i j, permSubsystemsHom_eq_permHom]
    simp [Matrix.mul_apply]
    rw [Equiv.Perm.one_def]
    rw [Equiv.refl_symm]
    simp
    -- dude.
    sorry

  | succ n hi =>
    simp? [QFTRevCircuit]
    ext a b
    simp only [hi]
    simp only [QFTRev_apply]
    push_cast
    simp only [stdAddChar_coe]





    sorry


noncomputable def QFTRevCircuit_qubit (n : ℕ) : 𝐔[Fin n → Fin 2] :=
  match n with
    | 0 => 1
    | (n+1) =>
      (single (Fin.last n) Qubit.H) * (CRCircuit 2) * (succ (QFTRevCircuit_qubit n))
