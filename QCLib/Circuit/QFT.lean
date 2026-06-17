module

public import QCLib.Circuit.Permutation
public import QCLib.Circuit.Gate.Qubit
public import QCLib.Circuit.Embed
public import QCLib.LinearAlgebra.OuterProduct



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


-- move out,
theorem reindexMonoidEquiv_smul_basis {m n : Type*}
    [DecidableEq m] [Fintype m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (U : 𝐔[m]) (w : n) :
    reindexMonoidEquiv e U • δ[w] = (U • δ[e.symm w]) ∘ e.symm := by
  ext
  simp [basisVector_def, Submonoid.smul_def]

namespace Register

/-
  A `Register` is first converted to `Fin (2 ^ n)` before being casted to `Int`.
  This preserves the information that the value is bounded by `2 ^ n`.

  This distinction matters because certain lemmas, such as `ζ_sum_ortho`, can be formulated
  only for Fin types and therefore cannot be applied directly to arbitrary integers.
-/

open Fin ComplexConjugate PiOuterProduct Qubit Matrix

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

private theorem ζ_aux (l : Fin n) (u : Fin (2 ^ n)) :
    (δ[0] + conj (ζ (2 ^ ((l : ℕ) + 1))) ^ (u : ℤ) • δ[1]) =
      ∑ j : Fin 2, conj ζ (2 ^ ((l : ℕ) + 1)) ^ (u * j : ℕ) • δ[j] := by
  simp [Pi.smul_def]

private theorem ζ_aux' (x : Register n) (u : Fin (2 ^ n)) :
   (∏ i : Fin n, conj ζ (2 ^ (i + 1 : ℕ)) ^ (u * (x i) : ℕ))
    = conj ζ (2 ^ n) ^ (u * equivFin x : ℤ) := by
  nth_rw 1 [equivFin_apply_reindex]
  norm_cast
  simp [ζ_pow_fin_rev, ← pow_mul, Finset.prod_pow_eq_pow_sum, ← mul_assoc, mul_comm, Finset.mul_sum]
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
  simp only [IQFT, Real.sqrt_inv, map_zpow₀, smul_of, of_apply, Pi.smul_apply, Complex.real_smul,
    Complex.ofReal_inv]

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
    with_reducible congr! with y
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

open UnitaryGroup Finset Function

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

theorem CR_eq_controlledR (h : i ≠ j) : CR i j k = bipartite i j C[R k] h := by
  simp [CR, CR_diagonal, bipartite_diagonal]

def CCR :=
  ((Ioi i).toList.attach.map
    (fun j : { x // x ∈ (Ioi i).toList } =>
      bipartite j.1 i C[R (j - i + 1)] (by aesop))).prod

theorem CCR_diagonal :
    CCR i = diagonal (fun v : Register n =>
      ∏ j ∈ Ioi i, (ζ (2 ^ (j - i + 1 : ℕ))) ^ (v j * v i : ℕ)) := by
  simp [CCR, ← CR_eq_controlledR, Function.comp_def, CR, ← Fisnet.prod_diagonal]
  grind

theorem CRR_inv_eq :
    (CCR i)⁻¹
    = diagonal (fun v : Register n =>
        ∏ j ∈ Ioi i, conj (ζ (2 ^ (j + 1 : ℕ))) ^ (2 ^ (i : ℕ) * v j * v i : ℕ)) := by
  apply star_injective
  simp only [inv_val, CCR_diagonal, star_diagonal, Pi.star_def, star_prod, star_pow,
    RCLike.star_def, RingHomCompTriple.comp_apply, RingHom.id_apply, diagonal_eq_diagonal_iff]
  intro k
  congr! 1 with x
  simp [ζ_def, ← Complex.exp_nat_mul, pow_succ, pow_sub₀ (2 : ℂ) (by simp) (show i ≤ x by grind)]
  grind

theorem CCR_inv_apply_basis (v : Register n) :
  (CCR i)⁻¹ • δ[v] =
    (∏ j ∈ Ioi i,
      (starRingEnd ℂ) (ζ (2 ^ (j + 1 : ℕ))) ^ (2 ^ (i : ℕ) * (v j) * (v i) : ℕ)) • δ[v] := by
  simp only [basisVector_def, Pi.basisFun_apply, Submonoid.smul_def, CRR_inv_eq,
    smul_eq_mulVec, mulVec_single, MulOpposite.op_one, col_diagonal, one_smul]
  ext w
  by_cases hw : w = v <;> simp_all

end CR

-- #check Finset.sum_equiv
-- variable {n : ℕ}
-- private theorem rev_IQFT_apply_basis (v : Register n) :
--     revCircuit Qubit n • IQFT n • δ[v] = √(2^n)⁻¹ • ⨂ l : Fin n, δ[(0 : Qubit)] +
--         conj (ζ (2 ^ (l + 1 : ℕ))) ^ (equivFin (revRegister v) : ℤ) • δ[1] := by
--   simp [IQFT_apply_basis, Finset.smul_sum, smul_comm, -zpow_natCast, ]
--   simp_rw [ζ_aux, piOuterProduct_univ_sum, piOuterProduct_smul_univ,
--     ← basisVector_eq_prod, ζ_aux']
--   simp [Finset.smul_sum]
--   rw [Finset.sum_equiv revRegister.symm]
--   · simp
--   · intro i _
--     congr 3
--     simp [Register.equivFin]


open List OuterProduct Equiv

variable {m : ℕ}

@[simps]
def finLEEquiv {m} (h : n ≤ m) : Fin n ≃ {j : Fin m // j.val < n} where
  toFun i := ⟨i.castLE h, i.isLt⟩
  invFun j := ⟨j.val, j.prop⟩
  left_inv i := by simp
  right_inv j := by simp

def embedFin (h : n ≤ m) (U : 𝐔[Register n]) : 𝐔[Register m] :=
  subtype (fun i : Fin m => i.val < n)
    (reindexMonoidEquiv (Equiv.piCongrLeft' _ (finLEEquiv h)) U)

theorem embedFin_self_eq (U : 𝐔[Register n]) : embedFin (le_refl n) U = U := by
  ext
  simp [embedFin, blockDiagonal_apply, funext_iff]
  congr

theorem embedFin_embedFin {k} (U : 𝐔[Register n]) (hn : n ≤ k) (hk : k ≤ m) :
    embedFin hk (embedFin hn U) = embedFin (le_trans hn hk) U := by
  ext a b
  simp [embedFin, blockDiagonal_apply, funext_iff, piCongrLeft']
  split_ifs with h1 h2 h3 <;> try grind
  obtain ⟨q, hq⟩ := not_forall.mp h3
  by_cases hkq : k ≤ q
  · have := h1 q
    simp_all
  · simp only [not_le] at hkq
    have := h2 ⟨q, hkq⟩
    exfalso
    exact hq (by simp_all)

theorem embedFin_smul (h : n ≤ m) (A U : 𝐔[Register n]) :
    embedFin h (A • U) = embedFin h A • embedFin h U := by
  ext
  simp [embedFin, ← blockDiagonal_mul]

def CIQFT_Rev (n) : 𝐔[Register n] :=
  match n with
  | 0 => 1
  | k + 1 =>
    single (last k) H • (CCR (last k))⁻¹ • embedFin (show k ≤ k + 1 by lia) (CIQFT_Rev k)

theorem embedFin_revCircuit (v : Register m) (h : n ≤ m) :
    embedFin h (revCircuit Qubit n) • δ[v] =
      δ[fun i : Fin m => if hi : i.val < n then v ((⟨i, hi⟩ : Fin n).rev.castLE h) else v i] := by
  simp only [embedFin, piCongrLeft', subtype_apply_basis, reindexMonoidEquiv_smul_basis, symm_mk,
    coe_fn_mk, finLEEquiv_apply_coe, revCircuit_apply]
  ext x
  simp only [basisVector_def, Pi.basisFun_apply, Function.comp_apply, piEquivPiSubtypeProd_apply,
    outerProduct_apply, finLEEquiv_apply_coe, Pi.single_apply, funext_iff, revRegister_apply,
    Subtype.forall, not_lt, mul_ite, mul_one, mul_zero]
  split_ifs with h1 h2 _ h3 <;> try grind
  obtain ⟨q, hq⟩ := not_forall.mp h2
  have := h3 (q.castLE h)
  simp_all

theorem embedFin_CIQFT_apply_basis (v : Register m) (h : n ≤ m) :
    embedFin h (CIQFT_Rev n • revCircuit Qubit n) • δ[v] =
      ((√(2^n)⁻¹ • ⨂ x : {j : Fin m // j.val < n},
        (δ[(0 : Qubit)] +
        (∏ i ∈ Finset.Iic x,
          conj (ζ (2 ^ (x + 1 : ℕ)) ^ (2 ^ (i : ℕ) * revRegister v i : ℕ))) • δ[1]))
          ⊗ (δ[fun i : {j : Fin m // ¬(j.val < n)} => v i.1])) ∘
          piEquivPiSubtypeProd _ _ := by
  rw [embedFin_smul, smul_assoc, embedFin_revCircuit]
  induction n with
  | zero =>
    haveI : IsEmpty {j : Fin m // j.val < 0} := by
      simp [Subtype.isEmpty_of_false]
    ext
    simp [embedFin, subtype, basisVector_def, Submonoid.smul_def,
      blockDiagonal_apply, Pi.single_apply, funext_iff, CIQFT_Rev, Matrix.one_apply]
  | succ n ih =>
    simp_rw [CIQFT_Rev, embedFin_smul, smul_assoc, embedFin_embedFin, ]
    generalize_proofs hnm
    sorry

-- theorem CIQFT_eq_IQFT : CIQFT n = IQFT n := by
--   rw [← embedFin_eq (CIQFT n)]
--   apply ext_smul_basis
--   intro v
--   rw [embedFin_CIQFT_apply_basis, IQFT_apply_basis'']
--   ext k
--   simp? [basisVector_def, Pi.single_apply, funext_iff] -- simp only = regret
--   apply Fintype.prod_equiv (finLEEquiv (n := n) (le_refl n)).symm
--   simp only [isValue, finLEEquiv, castLE_refl, Fin.eta, symm_mk, coe_fn_mk, Subtype.forall, is_lt,
--     forall_true_left]
--   intro a
--   split_ifs with h1 h2 h3 <;> simp <;> try grind
--   apply Finset.prod_equiv (finLEEquiv (le_refl n)).symm <;> aesop
