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
  nth_rw 1 [equivFin_apply_reindex]
  simp [hd.out, ζ_pow_fin_rev, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, ← mul_assoc, mul_comm, Finset.mul_sum]
  lia


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

end dftZMod


public section dftFin

variable (n d : ℕ) [hdz : NeZero d]

@[simps! -isSimp coe]
noncomputable def QFT : 𝐔[Fin n → Fin d] :=
  reindexMonoidEquiv (equivFin.trans (ZMod.finEquiv (d^n)).toEquiv).symm
    (UnitaryGroup.dftZMod (d ^ n))

@[simp] theorem QFT_apply (a b) :
    QFT n d a b = √(d ^ n)⁻¹ * (ζ (d ^ n)) ^ (equivFin a * equivFin b : ℕ) := by
  simp [QFT_coe, stdAddChar_apply, toCircle_apply,
    ← map_mul, ← div_mul_eq_mul_div, exp_nat_mul',
    show cexp (2 / ↑d ^ n * ↑π * I) = ζ (d ^ n) by grind [ζ_def],
    ζ_pow_mul]

theorem QFT_apply_basis (v : Fin n → Fin d) :
    QFT n d • δ[v] = ∑ k, (√(d ^ n)⁻¹ * (ζ (d ^ n)) ^ (equivFin v * equivFin k : ℕ)) • δ[k] := by
  ext w
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, smul_eq_mulVec, mulVec_single,
    MulOpposite.op_one, Pi.smul_apply, col_apply, QFT_apply, sqrt_inv, ofReal_inv, one_smul,
    Finset.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_single w] <;> grind

theorem QFT_apply_basis_product (v : Fin n → Fin d) :
    QFT n d • δ[v] =
      (√(d ^ n)⁻¹ : ℂ) •
        ⨂ (i : Fin n), ∑ j : Fin d, ζ (d ^ (i + 1 : ℕ)) ^ ((equivFin v) * j : ℕ) • δ[j] := by
  simp_rw [QFT_apply_basis, basisVector_eq_prod, ←smul_eq_mul, smul_assoc,
    ← Finset.smul_sum,]
  simp [← ζ_aux, ←piOuterProduct_smul_univ, ← piOuterProduct_univ_sum (ι := Fin n) (κ := Fin d)
    (f := fun i j => ζ (d ^ (↑i + 1 : ℕ)) ^ (↑(equivFin v) * (j : ℕ)) • δ[j])]
