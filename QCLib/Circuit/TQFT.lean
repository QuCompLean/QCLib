module

public import Mathlib.Analysis.Fourier.ZMod

public import QCLib.Circuit.Embed
public import QCLib.Circuit.Gate.Qubit
public import QCLib.Circuit.Permutation


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
        ∏ j ∈ (Ioi i).attach,
          star (uζ (d ^ (j + 1 : ℕ)) ^ (d ^ (i : ℕ) * (y i) * (y j) : ℕ)) := by
  simp only [CIRCircuit, CIR_at_diagonal, ← prod_diagonal]
  congr! 1
  apply List.map_congr_left (fun a h ↦ ?_)
  congr! 3
  simp [pow_mul, ← uζ_pow_sub hd.out (by grind : i.val ≤ a + 1)]

def CIRCircuit' (d) (i : Fin n) : 𝐔[Fin n → Fin d] :=
  ((Iio i.rev).attach.toList.map (
    fun j : ↥(Iio i.rev) ↦ bipartite j.val.rev i (controllize d (IR (j.val.rev + 1 - i)))
  )).prod

theorem CIRCircuit'_eq (i : Fin n) [hd : NeZero d] :
    CIRCircuit' d i =
      diagonalMonoidHom fun y : Fin n → Fin d ↦
        ∏ x ∈ (Iio i.rev).attach,
          star (uζ (d ^ ((x : Fin n).rev + 1 : ℕ))
            ^ (d ^ (↑i : ℕ) * (y i) * ((revRegister y) x) : ℕ)) := by
  simp only [CIRCircuit', CIR_at_diagonal, ← prod_diagonal]
  congr! 1
  apply List.map_congr_left (fun a h ↦ ?_)
  congr! 3
  simp only [pow_mul, ← uζ_pow_sub hd.out (show i.val ≤ a.val.rev + 1 by grind)]
  simp

theorem CIRCircuit'_eq_CIRCircuit (i : Fin n) [hd : NeZero d] :
    CIRCircuit' d i = CIRCircuit d i := by
  ext a b
  simp? [CIRCircuit'_eq, CIRCircuit_eq, -val_rev, -revRegister_apply]
  congr with x
  rw [Finset.prod_attach (s := (Iio i.rev)) (f := fun x_1 =>
    (starRingEnd ℂ) (ζ (d ^ (↑(x_1).rev + 1 : ℕ)))
    ^ (d ^ (i : ℕ) * ↑(x i) * ↑(revRegister x ↑x_1) : ℕ)),
    Finset.prod_attach (s := (Ioi i)) (f := fun x_1 =>
    (starRingEnd ℂ) (ζ (d ^ (↑↑x_1 + 1 : ℕ))) ^ (d ^ (i : ℕ) * ↑(x i) * ↑(x ↑x_1)))
  ]
  exact Finset.prod_equiv Fin.revPerm (by simp; grind) (by simp)

end CRCircuit


-- noncomputable section QFTCircuit

-- open UnitaryGroup OuterProduct Fin Finset

-- def IQFTRevCircuit (n d : ℕ) [NeZero d] : 𝐔[Fin n → Fin d] := match n with
--   | 0 => 1
--   | n + 1 =>
--     (single 0 (idftFin d)) * CIRCircuit d 0 * (embedRight (IQFTRevCircuit n d))

-- example (d : ℕ) [NeZero d] (v : Fin 2 → Fin d) : True := by
--   set s := IQFTRevCircuit 2 d • δ[v] with hs
--   simp only [IQFTRevCircuit, Nat.reduceAdd, isValue] at hs
--   simp_rw [←smul_eq_mul, smul_assoc, embedRight_apply_basis] at hs
--   simp at hs
--   trivial

-- def IQFTCircuit (n d : ℕ) [NeZero d] := IQFTRevCircuit n d * revCircuit (Fin d) n

-- theorem IQFTCircuit_eq_QFT (n d : ℕ) [hd : NeZero d] : IQFTCircuit n d = IQFT n d := by
--   rw [← mul_left_inj (revCircuit (Fin d) n), IQFTCircuit,
--     mul_assoc, revCircuit_involution, mul_one, revCircuit_eq_revPermSubsystems]
--   induction n with
--   | zero =>
--     ext i j
--     simp [IQFTRevCircuit, Subsingleton.elim i j]
--   | succ n ih =>
--     sorry
--     apply ext_smul_basis
--     intro v
--     simp_rw [QFTRevCircuit, ih, ← smul_eq_mul, smul_assoc, last_single_succ_apply_basis]
--     ext a
--     simp? [permSubsystemsHom_smul_unitary_smul_basis,
--       Function.comp_def, CRCircuit_eq, dftFin_apply_basis]
--     simp? [Submonoid.smul_def,
--       basisVector_def, Pi.single_apply, mulVec_eq_sum, diagonal_apply]
--     field_simp
--     simp [show (√(d ^ n) * √d) = (√(d ^ (n + 1)) : ℂ) by simp [pow_succ],
--       div_left_inj' (show (√(d ^ (n + 1)) : ℂ) ≠ 0 by simp [hd.out]),
--       show (Finset.Ioi (last n)).attach = ({} : Finset _) by grind
--     ]
--     simp [equivFin, Fin.sum_univ_castSucc, add_mul, mul_add]
