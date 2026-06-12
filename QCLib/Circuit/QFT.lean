module

public import QCLib.Circuit.Permutation
public import QCLib.Circuit.Gate.Qubit
public import QCLib.Circuit.Embed




@[expose] public noncomputable section

open Fin ComplexConjugate PiOuterProduct Qubit Matrix

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

open Register

variable {n : ℕ}

section Aux

private theorem ζ_aux (l : Fin n) (v : Register n) :
    (δ[0] + conj (ζ (2 ^ ((l : ℕ) + 1))) ^ (equivFin v : ℤ) • δ[1]) =
      ∑ j : Fin 2, conj ζ (2 ^ ((l : ℕ) + 1)) ^ (equivFin v * j : ℕ) • δ[j] := by
  simp [Pi.smul_def]

private theorem ζ_aux' (v x : Register n) :
   (∏ i : Fin n, conj ζ (2 ^ (i + 1 : ℕ)) ^ (equivFin v * (x i) : ℕ))
    = conj ζ (2 ^ n) ^ (equivFin v * equivFin x : ℤ) := by
  nth_rw 3 [equivFin_apply_reindex]
  norm_cast
  simp [ζ_pow_fin_rev, ← pow_mul, Finset.prod_pow_eq_pow_sum, ← mul_assoc, mul_comm, Finset.sum_mul]
  lia

end Aux


section IQFT

def IQFT (n : ℕ) : 𝐔[Register n] :=
  ⟨√(2^n)⁻¹ • of fun a b => conj (ζ (2^n) ^ (equivFin a * equivFin b : ℤ)), by
    rw [mem_unitaryGroup_iff, star_smul, star_trivial, smul_mul_smul]
    ext i j
    have (x : Fin (2^n)) (y) := mul_comm (conj (ζ (2^n) ^ (equivFin i * x : ℤ))) y
    simp_all [← mul_inv, mul_apply, one_apply,
      sum_register_univ_eq, show i = j ↔ j = i from Eq.comm]
  ⟩

@[simp]
theorem IQFT_apply (a b : Register n) :
    IQFT n a b = √(2^n)⁻¹ * conj (ζ (2^n)) ^ (equivFin a * equivFin b : ℤ) := by
  simp [IQFT]

theorem IQFT_apply_basis (v : Register n) :
    IQFT n • δ[v] = ∑ k, (√(2^n)⁻¹ * conj (ζ (2^n)) ^ (equivFin v * equivFin k : ℤ)) • δ[k] := by
  ext a
  by_cases ha : a = v <;>
    simp [basisVector_def, ha, Pi.single_apply, IQFT, mul_comm]

theorem IQFT_apply_basis' (v : Register n) :
    IQFT n • δ[v] =
      √(2^n)⁻¹ • ⨂ l : Fin n, δ[(0 : Qubit)] +
        conj (ζ (2 ^ (l + 1 : ℕ))) ^ (equivFin v : ℤ) • δ[1] := by
  simp_rw [IQFT_apply_basis, ζ_aux, piOuterProduct_univ_sum, piOuterProduct_smul_univ,
    ← basisVector_eq_prod, ζ_aux']
  simp [Finset.smul_sum]

theorem IQFT_apply_basis'' (v : Register n) :
    IQFT n • δ[v] =
      √(2^n)⁻¹ • ⨂ x : Fin n, (δ[(0 : Qubit)] + (∏ i ∈ Finset.Iic x,
        conj (ζ (2 ^ (x + 1 : ℕ)) ^ (2 ^ (i : ℕ) * revRegister v i : ℕ))) • δ[1]) := by
  by_cases hn : n = 0
  · subst hn; ext k; simp [IQFT, basisVector_def]
  · rw [IQFT_apply_basis']
    congr! with y
    apply (starRingEnd ℂ).injective
    simp only [← coe_uζ, zpow_natCast, map_pow, RingHomCompTriple.comp_apply,
      RingHom.id_apply, revRegister_apply, Finset.prod_pow_eq_pow_sum]
    norm_cast
    apply pow_eq_pow_iff_modEq.mpr
    simp only [orderOf_uζ, equivFin_apply, finFunctionFinEquiv_apply_val, Equiv.piCongrLeft'_apply,
      revPerm_symm, revPerm_apply, sum_univ_eq_sum_Iic_add_sum_Ioi y,  mul_comm,
      Nat.add_modEq_left_iff]
    apply Finset.dvd_sum (fun i hi => ?_)
    generalize v i.rev = a
    fin_cases a <;> simp_all [Nat.pow_dvd_pow]

end IQFT


section CIQFT

open UnitaryGroup List

public section CR

theorem R_diagonal (k) :
    R k = diagonalMonoidHom fun a : Qubit ↦ (uζ (2 ^ k)) ^ (a : ℕ) := by
  matrix_expand

theorem CR_diagonal (k) :
    C[R k] = diagonalMonoidHom (fun a ↦ (uζ (2 ^ k)) ^ (a.2 * a.1 : ℕ)) := by
  simp [R_diagonal, controllize_diagonal, pow_mul]

variable (i j : Fin n) (k : ℕ)

def CR : 𝐔[Register n] :=
  diagonalMonoidHom (fun a : Register n ↦ (uζ (2 ^ k)) ^ (a j * a i : ℕ))

theorem CR_eq_controlled (h : i ≠ j) : CR i j k = bipartite i j C[R k] h := by
  simp [CR, CR_diagonal, bipartite_diagonal]

end CR
