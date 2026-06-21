module

public import Mathlib.Analysis.Fourier.ZMod

public import QCLib.Circuit.Embed
public import QCLib.Circuit.Gate.Qubit
public import QCLib.Circuit.Permutation
public import QCLib.Circuit.EmbedFin

open ZMod Matrix.UnitaryGroup ComplexConjugate Matrix Complex Real PiOuterProduct Fin Equiv

public section Aux

theorem Complex.exp_nat_mul' (x : ℂ) (n : ℕ) :
    cexp (x * n) = cexp (x) ^ n := by
  simp [← Complex.exp_nat_mul, mul_comm]

@[simp]
theorem finEquiv_val {n} [NeZero n] (a : Fin n) :
    (finEquiv n a).val = ↑a := by
  cases n with
  | zero => exact Fin.elim0 a
  | succ n => rfl

lemma ζ_pow_mul {n} [NeZero n] (a b : Fin n) :
    ζ n ^ ((a * b : Fin n) : ℕ) = ζ n ^ ((a : ℕ) * (b : ℕ)) := by
  rw [← coe_uζ]
  norm_cast
  exact pow_eq_pow_iff_modEq.mpr
    (by simpa [orderOf_uζ, Fin.val_mul] using Nat.mod_modEq _ _)

lemma ζ_pow_add (a b c) :
    ζ a ^ (b + c) = ζ a ^ b * ζ a ^ c := by
  simp [pow_add]

@[simps! -isSimp apply, expose]
def equivFin {n d : ℕ} : (Fin n → Fin d) ≃ Fin (d ^ n) :=
  (arrowCongrLeftHom (Fin d) Fin.revPerm).trans finFunctionFinEquiv

lemma equivFin_apply_reindex {n d} [NeZero d] (v : Fin n → Fin d) :
    ((equivFin v) : ℕ) = ∑ i : Fin n, (v i : ℕ) * d ^ (n - 1 - i : ℕ) := by
  simp only [equivFin_apply, finFunctionFinEquiv_apply_val, arrowCongr_apply, coe_refl,
    revPerm_symm, Function.comp_apply, revPerm_apply, id_eq]
  apply Finset.sum_equiv Fin.revPerm (by simp) (fun i _ => ?_)
  simp only [revPerm_apply, val_rev, mul_eq_mul_left_iff, val_eq_zero_iff]
  left
  congr
  lia

open AddChar in
theorem stdChar_orthogonal (N : ℕ) [NeZero N] (t s : ZMod N) :
    ∑ x, stdAddChar (t * x) * conj (stdAddChar (s * x)) = if t = s then ↑N else 0 := by
  simp [← inv_apply_eq_conj, ← inv_apply', ← map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul, mul_comm,
    AddChar.sum_mulShift _ (isPrimitive_stdAddChar N), sub_eq_zero]

-- Relocate
theorem reindexMonoidEquiv_smul_basis {m n : Type*}
    [DecidableEq m] [Fintype m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (U : 𝐔[m]) (w : n) :
    reindexMonoidEquiv e U • δ[w] = (U • δ[e.symm w]) ∘ e.symm := by
  ext
  simp [basisVector_def, Submonoid.smul_def]

end Aux


section private_aux

open Finset

variable {n d : ℕ} [hd : NeZero d]

private theorem ζ_aux (x : Fin n → Fin d) (u : Fin (d ^ n)) :
   (∏ i : Fin n, ζ (d ^ (i + 1 : ℕ)) ^ (u * (x i) : ℕ))
    =  ζ (d ^ n) ^ (u * equivFin x : ℕ) := by
  rw [equivFin_apply_reindex]
  simp [hd.out, ζ_pow_fin_rev, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, ← mul_assoc, mul_comm, Finset.mul_sum]
  lia

lemma prod_star_uζ (d n : ℕ) (i : Fin n) (y : Fin n → Fin d) [hd : NeZero d] :
    ∏ j ∈ Finset.Ioi i, star (uζ (d ^ (j + 1 : ℕ))) ^ (d ^ (i : ℕ) * y i * y j) =
      star (uζ (d ^ n)) ^ (∑ j ∈ Finset.Ioi i, (d ^ (j.rev + i : ℕ) * y i * y j)) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  congr! 1 with j
  simp_rw [uζ_pow_fin_rev d n j hd.out, star_pow, ← pow_mul, ←mul_assoc, pow_add]

--relocate  (not used)
theorem prod_Ioi_castSucc (i : Fin n) {M} [CommMonoid M] (f : Fin (n + 1) → M) :
    ∏ i ∈ (Ioi i.castSucc), f i = (∏ j ∈ (Ioi i), f j.castSucc) * f (last n):= by
  rw [show Finset.Ioi i.castSucc =
    insert (Fin.last n) (Finset.map Fin.castSuccEmb (Finset.Ioi i)) by aesop,
    Finset.prod_insert (by aesop), Finset.prod_map]
  simp [mul_comm]

--relocate (not used)
theorem List.prod_mul_distrib_of_commute {M : Type*} [Monoid M] {ι : Type*}
    (l : List ι) (hl : l.Nodup) (A B : ι → M)
    (hcomm : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → Commute (B x) (A y)) :
    (l.map (fun i ↦ A i * B i)).prod = (l.map A).prod * (l.map B).prod := by
  induction l with
  | nil => simp
  | cons x xs IH =>
    simp_all
    grind [show Commute (B x) (xs.map A).prod
      by grind [Commute.list_prod_right]]


end private_aux


public noncomputable section dftZMod

variable (N : ℕ) [NeZero N]

/-- The matrix representation of the inverse DFT for `ZMod N`, also known as the *Schur matrix* -/
def Matrix.dftZMod : Matrix (ZMod N) (ZMod N) ℂ :=
  of fun i j ↦ conj ((dft (Pi.single j 1)) i)

@[simp]
theorem Matrix.dftZMod_apply_apply (i j : ZMod N) : dftZMod N i j = stdAddChar (i * j) := by
  simp [dftZMod, ← AddChar.map_neg_eq_conj, dft_apply, Pi.single_apply, mul_comm]

@[simps coe, expose]
def UnitaryGroup.dftZMod : 𝐔[ZMod N] := ⟨√(N⁻¹) • _root_.Matrix.dftZMod N, by
  simp only [Real.sqrt_inv, mem_unitaryGroup_iff, star_smul, star_trivial, Algebra.mul_smul_comm,
    Algebra.smul_mul_assoc, smul_assoc_symm, smul_eq_mul,
    show (√↑N)⁻¹ * (√↑N)⁻¹ = (N : ℝ)⁻¹ by grind]
  ext
  simp [Matrix.mul_apply, Matrix.one_apply, stdChar_orthogonal] ⟩

@[simps! -isSimp coe]
def UnitaryGroup.dftFin : 𝐔[Fin N] :=
  reindexMonoidEquiv (ZMod.finEquiv N).symm (dftZMod N)

@[simp]
theorem UnitaryGroup.dftFin_apply (a b) : dftFin N a b = √N⁻¹ • ζ N ^ (a * b : ℕ) := by
  simp [dftFin_coe, stdAddChar_apply, toCircle_apply, ← map_mul,
    ← div_mul_eq_mul_div, exp_nat_mul', show cexp (2 / N * ↑π * I) = ζ N by grind [ζ_def],
    ζ_pow_mul]

theorem UnitaryGroup.dftFin_apply_basis (v : Fin N) :
    dftFin N • δ[v] = ∑ k : Fin N, (√N⁻¹ * ζ N ^ (k * v : ℕ)) • δ[k] := by
  ext
  simp [basisVector_def, Submonoid.smul_def, Pi.single_apply]

def UnitaryGroup.idftFin : 𝐔[Fin N] := star (dftFin N)

@[simp]
theorem UnitaryGroup.idftFin_apply (a b) : idftFin N a b = √N⁻¹ • conj (ζ N ^ (a * b : ℕ)) := by
  simp [idftFin, mul_comm]

@[simp]
theorem UnitaryGroup.idftFin_apply_basis (v : Fin N) :
    idftFin N • δ[v] = ∑ k : Fin N, (√N⁻¹ * conj (ζ N ^ (k * v : ℕ))) • δ[k] := by
  ext
  simp [basisVector_def, Submonoid.smul_def, Pi.single_apply]

end dftZMod


public section QFT

variable (n d : ℕ) [hdz : NeZero d]

noncomputable def QFT : 𝐔[Fin n → Fin d] :=
  reindexMonoidEquiv equivFin.symm (UnitaryGroup.dftFin (d ^ n))

@[simp] theorem QFT_apply (a b) :
    QFT n d a b = √(d ^ n)⁻¹ * (ζ (d ^ n)) ^ (equivFin a * equivFin b : ℕ) := by
  simp [QFT]

theorem QFT_apply_basis (v : Fin n → Fin d) :
    QFT n d • δ[v] = ∑ k, (√(d ^ n)⁻¹ * (ζ (d ^ n)) ^ (equivFin v * equivFin k : ℕ)) • δ[k] := by
  ext w
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, QFT_apply, sqrt_inv, ofReal_inv, one_smul,
    Finset.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_single w] <;> grind

theorem QFT_apply_product_basis (v : Fin n → Fin d) :
    QFT n d • δ[v] =
      (√(d ^ n)⁻¹ : ℂ) •
        ⨂ (i : Fin n), ∑ j : Fin d, ζ (d ^ (i + 1 : ℕ)) ^ ((equivFin v) * j : ℕ) • δ[j] := by
  simp_rw [QFT_apply_basis, basisVector_eq_prod, ← smul_eq_mul, smul_assoc]
  simp [← Finset.smul_sum, ← ζ_aux, ← piOuterProduct_smul_univ, piOuterProduct_univ_sum]

end QFT


public section IQFT

variable (n d : ℕ) [hdz : NeZero d]

noncomputable def IQFT : 𝐔[Fin n → Fin d] := star (QFT n d)

@[simp] theorem IQFT_apply (a b) :
    IQFT n d a b = √(d ^ n)⁻¹ * conj ((ζ (d ^ n)) ^ (equivFin a * equivFin b : ℕ)) := by
  simp [IQFT, mul_comm]

theorem IQFT_apply_basis (v : Fin n → Fin d) :
    IQFT n d • δ[v] =
      ∑ k, (√(d ^ n)⁻¹ * conj ((ζ (d ^ n)) ^ (equivFin v * equivFin k : ℕ))) • δ[k] := by
  ext w
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, IQFT_apply, sqrt_inv, ofReal_inv, one_smul,
    Finset.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_single w] <;> grind

theorem IQFT_apply_product_basis (v : Fin n → Fin d) :
    IQFT n d • δ[v] =
      (√(d ^ n)⁻¹ : ℂ) • ⨂ (i : Fin n),
        ∑ j : Fin d, conj (ζ (d ^ (i + 1 : ℕ)) ^ ((equivFin v) * j : ℕ)) • δ[j] := by
  simp_rw [IQFT_apply_basis, basisVector_eq_prod, ← smul_eq_mul, smul_assoc]
  simp [← Finset.smul_sum, ← ζ_aux, ← piOuterProduct_smul_univ,
     piOuterProduct_univ_sum]

end IQFT


public noncomputable section CRCircuit

open Finset

variable {d n : ℕ} (k : ℕ)

def IR : 𝐔[Fin d] :=
  diagonalMonoidHom (fun x ↦ star ((uζ (d ^ k)) ^ (x : ℕ)))

theorem CIR_diagonal :
    controllize d (IR k) =
      diagonalMonoidHom (fun x : Fin d × Fin d ↦
        star (uζ (d ^ k)) ^ (x.2 * x.1 : ℕ)) := by
  simp [IR, controllize_diagonal, pow_mul]

theorem CIR_at_diagonal (i j : Fin n) (hneq : i ≠ j) {d : ℕ} (k : ℕ) :
    bipartite i j (controllize d (IR k)) hneq =
      diagonalMonoidHom (fun x : Fin n → Fin d ↦ star (uζ (d ^ k) ^ (x j * x i : ℕ))) := by
  simp [CIR_diagonal, bipartite_diagonal]

def CIRCircuit (d) (i : Fin n) : 𝐔[Fin n → Fin d] :=
  ((Ioi i).attach.toList.map (
    fun j : ↥(Ioi i) ↦ bipartite j.val i (controllize d (IR (j + 1 - i)))
  )).prod

theorem CIRCircuit_eq (i : Fin n) [hd : NeZero d] :
    CIRCircuit d i =
      diagonalMonoidHom fun y : Fin n → Fin d ↦
          star (uζ (d ^ n)) ^ (∑ j ∈ Finset.Ioi i, (d ^ (j.rev + i : ℕ) * y i * y j)) := by
  simp_rw [←  prod_star_uζ (hd := hd), ← Finset.prod_attach (s := Ioi i), CIRCircuit,
    CIR_at_diagonal, ← prod_diagonal, ← star_pow]
  congr! 1
  apply List.map_congr_left (fun a h ↦ ?_)
  congr! 2
  simp [pow_mul, ← uζ_pow_sub hd.out (by grind : i.val ≤ a + 1)]

end CRCircuit


public noncomputable section IQFTCircuit

open UnitaryGroup OuterProduct

def IQFTRevCircuit (n d : ℕ) [NeZero d] : 𝐔[Fin n → Fin d] := match n with
  | 0 => 1
  | n + 1 =>
    (single 0 (idftFin d)) * CIRCircuit d 0 * (embedRight (IQFTRevCircuit n d))

example (d : ℕ) [NeZero d] (v : Fin 2 → Fin d) : True := by
  set s := IQFTRevCircuit 2 d • δ[v] with hs
  simp only [IQFTRevCircuit, Nat.reduceAdd, isValue] at hs
  simp_rw [←smul_eq_mul, smul_assoc, embedRight_apply_basis] at hs
  simp at hs
  trivial

def IQFTCircuit (n d : ℕ) [NeZero d] := IQFTRevCircuit n d * revCircuit (Fin d) n

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

private lemma ζ_pow_succ' (a k : ℕ) (ha : a ≠ 0) :
    ζ (a ^ (k + 1)) ^ a = ζ (a ^ k) := by
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  simp only [ζ, ← Complex.exp_nat_mul]
  congr 1
  push_cast [pow_succ]
  field_simp

private lemma ζ_pow_eq (a b c : ℕ) [NeZero a] :
    ζ a ^ b = ζ a ^ c ↔ b ≡ c [MOD a] := by
  rw [← coe_uζ]
  norm_cast
  simp [pow_eq_pow_iff_modEq]

set_option linter.flexible false in

theorem IQFTCircuit_eq_QFT (n d : ℕ) [hd : NeZero d] : IQFTCircuit n d = IQFT n d := by
  rw [← mul_left_inj (revCircuit (Fin d) n), IQFTCircuit,
    mul_assoc, revCircuit_involution, mul_one, revCircuit_eq_revPermSubsystems]
  induction n with
  | zero =>
    ext i j
    simp [IQFTRevCircuit, Subsingleton.elim i j]
  | succ n ih =>
    apply ext_smul_basis
    intro v
    simp_rw [IQFTRevCircuit, ih, ← smul_eq_mul, smul_assoc, embedRight_apply_basis]
    ext a
    simp [Function.comp_def, -permSubsystemsHom_smul_basis, CIRCircuit_eq]
    simp [basisVector_def, Submonoid.smul_def, mulVec_eq_sum, blockDiagonal_apply, funext_iff]
    simp [Pi.single_apply, ← ite_and, cons_iff]

    apply (starRingEnd ℂ).injective
    field_simp
    simp [show (√d * √(d ^ n)) = (√(d ^ (n + 1)) : ℂ) by simp [pow_succ'],
      div_left_inj' (show (√(d ^ (n + 1)) : ℂ) ≠ 0 by simp [hd.out])]

    simp [← ζ_pow_succ d n hd.out,  ← ζ_pow_succ' d n hd.out, ← pow_mul, ← pow_add, equivFin]
    nth_rw 2 [Fin.sum_univ_succ]
    simp [Fin.sum_univ_castSucc, Fin.rev_castSucc, mul_add, add_mul, ζ_pow_eq]

    have hE0 : ∑ x : Fin n, d ^ (n - (x + 1)) * (v 0 : ℕ) * (a x.succ)
            = (∑ x : Fin n, (a x.rev.succ) * d ^ (x : ℕ)) * (v 0) := by
      rw [Finset.sum_mul]
      refine Finset.sum_equiv Fin.revPerm (fun i => by simp) fun i _ => ?_
      simp only [Fin.revPerm_apply, Fin.rev_rev, Fin.val_rev]
      ring

    have hS1 : ∑ x : Fin n, (v x.succ : ℕ) * d ^ ((x:ℕ) + 1) =
      d * ∑ x : Fin n, (v x.succ : ℕ) * d ^ (x : ℕ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [pow_succ]; ring

    have hgap :
        (∑ x : Fin n, (a x.rev.succ) * d ^ (x : ℕ)) * (v 0) + (a 0) * d ^ n * (v 0) +
          ((∑ x  : Fin n, (a x.rev.succ:ℕ) * d ^ (x:ℕ)) * ∑ x  : Fin n, (v x.succ) * d ^ ((x:ℕ)+1) +
            (a 0) * d ^ n * ∑ x  : Fin n, (v x.succ) * d ^ ((x : ℕ) + 1))
      = ((∑ x : Fin n , (a x.rev.succ) * d ^ (x : ℕ)) * (v 0) + d ^ n * ((a 0) * (v 0)) +
          d * ((∑ x  : Fin n, (a x.rev.succ) * d ^ (x : ℕ)) * ∑ x : Fin n, (v x.succ:ℕ) * d ^ (x : ℕ)))
        + d ^ (n + 1) * ((a 0) * ∑ x : Fin n, (v x.succ) * d ^ (x : ℕ)) := by
      rw [hS1]; ring

    rw [hE0, hgap]
    exact (Nat.add_mul_mod_self_left _ _ _).symm
