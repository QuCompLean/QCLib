module

public import QCLib.LinearAlgebra.UnitaryGroup.stdAddChar
public import QCLib.Circuit.Permutation


@[expose] public noncomputable section

open Matrix Qubit Fin PiOuterProduct

/-- Identifies a binary tuple as a number. Unlike `finFunctionFinEquiv`,
  in the `equivFin` the most significant bit is at 0-th position. -/
@[simps! -isSimp apply symm_apply]
def Register.equivFin {n : ℕ} : Register n ≃ Fin (2 ^ n) :=
  (Equiv.piCongrLeft' _ revPerm).trans finFunctionFinEquiv

/- Note that `equivFin_apply` gives `∑ i, v (rev i) * 2 ^ i`. -/
lemma Register.equivFin_apply_reindex {n} (v : Register n) :
    ((Register.equivFin v) : ℕ) = ∑ i : Fin n, (v i : ℕ) * 2 ^ (n - 1 - i : ℕ) := by
  simp only [equivFin_apply, finFunctionFinEquiv_apply_val, Equiv.piCongrLeft'_apply, revPerm_symm,
    revPerm_apply]
  apply Finset.sum_equiv Fin.revPerm (by simp) (fun i _ => ?_)
  simp
  lia

lemma Finset.sum_register_univ_eq {n} {M : Type*} [AddCommMonoid M] (f : Register n → M) :
    ∑ r : Register n, f r = ∑ i, f (Register.equivFin.symm i) :=
  Finset.sum_equiv Register.equivFin (by simp) (by simp)


section QFT

open Register

variable {n : ℕ}

/-- Quantum fourier transformation as a unitary matrix. -/
def QFT (n : ℕ) : 𝐔[Register n] :=
  ⟨√(2 ^ n)⁻¹ • of fun a b => ζ(equivFin a * equivFin b), by
    rw [mem_unitaryGroup_iff, star_smul, star_trivial, smul_mul_smul]
    ext
    simp_all [← mul_inv, mul_apply, one_apply, Finset.sum_register_univ_eq]
  ⟩

@[simp]
theorem QFT_apply (a b : Register n) :
    QFT n a b = √(2 ^ n)⁻¹ * ζ(equivFin a * equivFin b) := by
  simp [QFT]

theorem QFT_apply_basis (v : Register n) :
    QFT n • δ[v] = ∑ k, (√(2 ^ n)⁻¹ * ζ(equivFin v * equivFin k)) • δ[k] := by
  ext a
  by_cases ha : a = v <;>
    simp [basisVector_def, ha, Pi.single_apply, QFT, mul_comm]
