module

public import QCLib.Circuit.Permutation
public import QCLib.Circuit.Gate.Qubit
public import QCLib.Circuit.Embed

@[expose] public noncomputable section

open Matrix Fin

/- move out. -/
theorem Fin.sum_univ_eq_sum_Iic_add_sum_Ioi
  {α} [Fintype α] [LinearOrder α] [LocallyFiniteOrderBot α]
  [LocallyFiniteOrderTop α] {β : Type*} [AddCommMonoid β] (x : α) (f : α → β) :
    ∑ i : α, f i = (∑ i ∈ Finset.Iic x, f i) + (∑ i ∈ Finset.Ioi x, f i) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ≤ x)]
  congr <;> ext i <;> simp [Finset.mem_Iic, Finset.mem_Ioi]

namespace Register

/-
  A `Register` is first converted to `Fin (2 ^ n)` before being casted to `Int`.
  This preserves the information that the value is bounded by `2 ^ n`.

  This distinction matters because certain lemmas, such as `ζ_sum_ortho`, can be formulated
  only for Fin types and therefore cannot be applied directly to arbitrary integers.
-/

/-- Identifies a binary tuple as a number. Unlike `finFunctionFinEquiv`,
  in the `equivFin` the most significant bit is at 0-th position. -/
@[simps! -isSimp apply symm_apply]
def equivFin {n : ℕ} : Register n ≃ Fin (2 ^ n) :=
  (Equiv.piCongrLeft' _ revPerm).trans finFunctionFinEquiv

/- Note that `equivFin_apply` gives `∑ i, v (rev i) * 2 ^ i`. -/
lemma equivFin_apply_reindex {n} (v : Register n) :
    ((equivFin v) : ℕ) = ∑ i : Fin n, (v i : ℕ) * 2 ^ (n - 1 - i : ℕ) := by
  simp only [equivFin_apply, finFunctionFinEquiv_apply_val, Equiv.piCongrLeft'_apply, revPerm_symm,
    revPerm_apply]
  apply Finset.sum_equiv Fin.revPerm (by simp) (fun i _ => ?_)
  simp
  lia

lemma sum_register_univ_eq {n} {M : Type*} [AddCommMonoid M] (f : Register n → M) :
    ∑ r : Register n, f r = ∑ i, f (equivFin.symm i) :=
  Finset.sum_equiv equivFin (by simp) (by simp)


end Register


section QFT

open Register


def QFTInv (n : ℕ) : 𝐔[Register n] :=
  ⟨√(2^n)⁻¹ • of fun a b => (starRingEnd ℂ) (ζ (2^n) ^ (equivFin a * equivFin b : ℤ)), by
    rw [mem_unitaryGroup_iff, star_smul, star_trivial, smul_mul_smul]
    ext i j
    have (x : Fin (2^n)) (y) := mul_comm ((starRingEnd ℂ) (ζ (2^n) ^ (equivFin i * x : ℤ))) y
    simp_all [← mul_inv, mul_apply, one_apply, sum_register_univ_eq, show i = j ↔ j = i from Eq.comm]
  ⟩
