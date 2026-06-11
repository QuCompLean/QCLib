module

public import QCLib.LinearAlgebra.UnitaryGroup.stdAddChar
public import QCLib.Circuit.Permutation


@[expose] public noncomputable section

open Matrix Qubit Fin

section explicitDef

/-
  A `Register` is first converted to `Fin (2 ^ n)` before being casted to `Int`.
  This preserves the information that the value is bounded by `2 ^ n`.

  This distinction matters because certain lemmas, such as `ζ_sum_ortho`, can be formulated
  only for Fin types and therefore cannot be applied directly to arbitrary integers.
-/

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

open Register

/-- Quantum fourier transformation as a unitary matrix. -/
def QFT (n : ℕ) : 𝐔[Register n] :=
  ⟨√(2 ^ n)⁻¹ • of fun a b => ζ(equivFin a * equivFin b), by
    rw [mem_unitaryGroup_iff, star_smul, star_trivial, smul_mul_smul]
    ext
    simp_all [← mul_inv, Matrix.mul_apply, Matrix.one_apply, Finset.sum_register_univ_eq]
  ⟩
