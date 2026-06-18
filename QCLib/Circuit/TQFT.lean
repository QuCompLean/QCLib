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


-- To be removed, if possible
section private_aux

variable {n d : ℕ} [hd : NeZero d]

private theorem ζ_aux (x : Fin n → Fin d) (u : Fin (d ^ n)) :
   (∏ i : Fin n, ζ (d ^ (i + 1 : ℕ)) ^ (u * (x i) : ℕ))
    =  ζ (d ^ n) ^ (u * equivFin x : ℕ) := by
  rw [equivFin_apply_reindex]
  simp [hd.out, ζ_pow_fin_rev, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, ← mul_assoc, mul_comm, Finset.mul_sum]
  lia

private theorem uζ_aux (x : Fin n.succ → Fin d) :
    (uζ (d ^ n)) ^ ((∑ i ∈ (Finset.Ioi (Fin.last n)).attach,
      d ^ (i : ℕ) * (x i) * (x (Fin.last n)))) =
    ∏ i ∈ (Finset.Ioi (Fin.last n)).attach,
      (uζ (d ^ (n - i))) ^ (((x i) * (x (Fin.last n))) : ℕ)
    := by
  rw [← Finset.prod_pow_eq_pow_sum]
  congr
  ext i
  simp [uζ_pow_sub hd.out (show i ≤ n by grind), pow_mul]

end private_aux


public section dftZMod

variable (N : ℕ) [NeZero N]

/-- The matrix representation of the inverse DFT for `ZMod N`, also known as the *Schur matrix* -/
noncomputable def Matrix.dftZMod : Matrix (ZMod N) (ZMod N) ℂ :=
  of fun i j ↦ conj ((dft (Pi.single j 1)) i)

@[simp]
theorem Matrix.dftZMod_apply_apply (i j : ZMod N) : dftZMod N i j = stdAddChar (i * j) := by
  simp [dftZMod , ← AddChar.map_neg_eq_conj, dft_apply, Pi.single_apply, mul_comm]

@[simps coe, expose]
noncomputable def UnitaryGroup.dftZMod : 𝐔[ZMod N] := ⟨√(N⁻¹) • _root_.Matrix.dftZMod N, by
    simp only [Real.sqrt_inv, mem_unitaryGroup_iff, star_smul, star_trivial, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_assoc_symm, smul_eq_mul,
      show (√↑N)⁻¹ * (√↑N)⁻¹ = (N : ℝ)⁻¹ by grind]
    ext
    simp [Matrix.mul_apply, Matrix.one_apply, stdChar_orthogonal] ⟩

@[simps! -isSimp coe]
noncomputable def UnitaryGroup.dftFin : 𝐔[Fin N] :=
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


public section CRCircuit

noncomputable def R {d : ℕ} (k : ℕ) : 𝐔[Fin d] :=
  diagonalMonoidHom (fun x ↦ (uζ (d ^ k)) ^ (x : ℕ))

theorem CR_diagonal {d : ℕ} (k : ℕ) :
    controllize d (R k) =
      diagonalMonoidHom (fun x : Fin d × Fin d ↦ (uζ (d ^ k)) ^ (x.2 * x.1 : ℕ)) := by
  simp [R, controllize_diagonal, pow_mul]

-- theorem CR_at_diagonal {n : ℕ} {i j : Fin n} (hneq : i ≠ j) {d : ℕ} (k : ℕ) :
--     bipartite i j (controllize d (R k)) hneq =
--       diagonalMonoidHom (fun x : Fin n → Fin d ↦ (uζ (d ^ k)) ^ (x j * x i : ℕ)) := by
--   simp [CR_diagonal, bipartite_diagonal]

-- noncomputable def CRCircuit {n : ℕ} (d : ℕ) : 𝐔[Fin (n + 1) → Fin d] :=
--   ((Finset.Ioi (Fin.last n)).attach.toList.map
--     fun i ↦ bipartite i.val (Fin.last n) (controllize d (R (n - i.val))) (by grind)).prod

-- theorem CRCircuit_eq_zero {n : ℕ} (d : ℕ) :
--     CRCircuit (n := n) d = 1 := by
--   simp [CRCircuit]
--   have : (Finset.Ioi (last n)).attach = ({} : Finset _) := by
--     grind
--   simp [this]


-- theorem CRCircuit_eq {n : ℕ} (d : ℕ) [NeZero d] :
--     CRCircuit d =
--       diagonalMonoidHom fun x : Fin n.succ → Fin d ↦
--         (uζ (d ^ n)) ^ ((∑ i ∈ (Finset.Ioi (Fin.last n)).attach,
--         d ^ (i : ℕ) * (x i) * (x (Fin.last n))) : ℕ) := by
--   simp_rw [CRCircuit, CR_at_diagonal, uζ_aux,
--     ← UnitaryGroup.prod_diagonal, mul_comm]

-- end CRCircuit


-- noncomputable section QFTCircuit

-- open UnitaryGroup OuterProduct

-- def QFTRevCircuit (n d : ℕ) [NeZero d] : 𝐔[Fin n → Fin d] :=
--   match n with
--   | 0 => 1
--   | n + 1 => (CRCircuit d) * (single (Fin.last n) (dftFin d)) * (succ (QFTRevCircuit n d))

-- def QFTCircuit (n d : ℕ) [NeZero d] := revCircuit (Fin d) n * QFTRevCircuit n d

-- theorem QFTCircuit_eq_QFT (n d : ℕ) [hd : NeZero d] : QFTCircuit n d = QFT n d := by
--   rw [← mul_right_inj (revCircuit (Fin d) n), QFTCircuit,
--     ← mul_assoc, revCircuit_involution, one_mul, revCircuit_eq_revPermSubsystems]
--   induction n with
--   | zero =>
--     ext i j
--     simp [QFTRevCircuit, Subsingleton.elim i j]
--   | succ n ih =>
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
