/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/

import QCLib.Circuit.PauliGroup.Generators

/-!

# The `n`-qubit Pauli group

## Main definitions

* `Pauli (p q : Fin n → ℤ)`: An element of the `n`-qubit Pauli group

## Main results

* `pauli_apply`: The group law.
* `pauli_apply`: Result of applying a Pauli group element to a basis vector

-/

open Qubit

variable {n : ℕ}

open Matrix Complex

open scoped PiOuterProduct

-- TBD: Could replace by `ᵤI`, but the theory also works for `τ = - ᵤI`.
/-- Fourth root of unity, bundled as a scalar unitary -/
noncomputable def τ : unitary ℂ := ᵤI

theorem tau_pow_two : τ^(2 : ℤ) = (-1) := by
  simp [τ]

@[simp]
theorem tau_pow_four : τ^(4 : ℤ) = 1 := by
  simp [τ]

@[simp]
theorem orderOf_tau : orderOf τ = 4 := by
  simp [τ]

@[simp]
theorem tau_eq_iff_mod_four_eq (y z : ℤ) :
   τ ^ y = τ ^ z ↔ y ≡ z [ZMOD ↑(4 : ℕ)] := orderOf_tau ▸ zpow_eq_zpow_iff_modEq

/-- Pauli group elements. -/
noncomputable def Pauli (p q : Fin n → ℤ) : unitaryGroup (Fin n → Fin 2) ℂ :=
τ ^ (p ⬝ᵥ q) • ((XX q) * (ZZ p))

theorem pauli_def (p q : Fin n → ℤ) : Pauli p q = τ ^ (p ⬝ᵥ q) • ((XX q) * (ZZ p)) :=
  rfl

@[simp]
theorem pauli_zero : Pauli (n := n) 0 0 = 1 := by simp [ZZ, XX, pauli_def]

-- TBD: Think about simp NF of `2 • p` vs `p * 2`
@[simp]
theorem pauli_even (p q : Fin n → ℤ) : Pauli (2 • p) (2 • q) = 1 := by
  simp [-nsmul_eq_mul, pauli_def, XX, ZZ, unitary_smul_free, orderOf_tau ▸ zpow_eq_one_iff_modEq]
  grind

-- TBD: define more globally
attribute [-simp] _root_.zpow_neg

theorem pauli_eq_prod (p q : Fin n → ℤ) :
    Pauli p q = ⨂ i, τ^(p i * q i) • (X ^ (q i) * Z ^ (p i)) := by
  simp [pauli_def, XX, ZZ, dotProduct, -Finset.sum_neg_distrib, ← Finset.prod_zpow_eq_zpow_sum,
    ← piKroneckerUnitary_smul_univ]

theorem ZZ_XX_anticomm (p q : Fin n → ℤ) :
    (ZZ p) * (XX q) = (ᵤ-1)^(p ⬝ᵥ q) • ((XX q) * (ZZ p)) := by
  simp [ZZ, XX, dotProduct, ← Finset.prod_zpow_eq_zpow_sum, ← piKroneckerUnitary_smul_univ,
    Z_zpow_X_zpow_anticomm]

theorem pauli_eq_ZZ_XX (p q : Fin n → ℤ) : Pauli p q = τ^(-p ⬝ᵥ q) • ((ZZ p) * (XX q)) := by
  simp [pauli_def, ZZ_XX_anticomm, ← tau_pow_two, ← _root_.zpow_mul, ← _root_.zpow_add]
  simp +arith -- TBD: Investigate weird error when adding `+arith` to first `simp` call

@[simp]
theorem pauli_comp (p p' : Fin n → ℤ) (q q' : Fin n → ℤ) :
    (Pauli p q) * (Pauli p' q') = τ^(p ⬝ᵥ q' - p' ⬝ᵥ q) • Pauli (p + p') (q + q') := by
  rw [pauli_eq_ZZ_XX, pauli_def, pauli_def, mul_smul_comm, unitary_smul_mul_nf, ← smul_assoc,
    ← mul_assoc]
  nth_rw 2 [mul_assoc]
  simp [ZZ_XX_anticomm, mul_assoc, ← tau_pow_two, ← _root_.zpow_mul, ← _root_.zpow_add]
  grind

theorem pauli_sq (p q : Fin n → ℤ) : (Pauli p q) * (Pauli p q) = 1 := by
  have (r : Fin n → ℤ) : r * 2 = 2 • r := by simp [mul_comm]
  simp only [pauli_comp, sub_self, zpow_zero, one_smul]
  ring_nf
  simp [-nsmul_eq_mul, this]

theorem pauli_comm_rel (p q p' q' : Fin n → ℤ) :
    (Pauli p q) * (Pauli p' q') = ᵤ-1^(p ⬝ᵥ q' - p' ⬝ᵥ q) • ((Pauli p' q') * (Pauli p q)) := by
  simp [add_comm, ← tau_pow_two, ← _root_.zpow_mul, ← _root_.zpow_add]
  grind
  -- `add_comm` dangerous in `simp`?

theorem pauli_comm_iff (p q p' q' : Fin n → ℤ) :
    Commute (Pauli p q) (Pauli p' q') ↔ (p ⬝ᵥ q' - p' ⬝ᵥ q) ≡ 0 [ZMOD 2] := by
  rw [commute_iff_eq, pauli_comm_rel, unitary_smul_free]
  apply orderOf_neg_one_eq_two ▸ zpow_eq_one_iff_modEq
  -- Is there some defeq abuse going on reg. (2 : ℕ) vs (2 : ℤ)?

-- TBD: State more cleanly?
theorem pauli_trace' (p q : ℤ) : trace (τ ^ (p * q) • (X ^ q * Z ^ p) : Matrix Qubit Qubit ℂ) =
    if Even p ∧ Even q then 2 else 0 := by
  simp only [trace_smul, X_zpow_Z_zpow_trace]
  by_cases h : Even p ∧ Even q
  · obtain ⟨x, hx⟩ := even_iff_exists_two_mul.mp h.1
    obtain ⟨y, hy⟩ := even_iff_exists_two_mul.mp h.2
    rw [hx, hy]
    ring_nf
    rw [mul_comm, _root_.zpow_mul]
    simp
  · simp [h]

-- TBD: State more cleanly?
theorem pauli_trace (p q : Fin n → ℤ) : trace ((Pauli p q) : (Matrix (Register n) (Register n) ℂ)) =
    if ∀ i, Even (p i) ∧ Even (q i) then 2 ^ n else 0 := by
  by_cases h : ∀ i, Even (p i) ∧ Even (q i)
  · push_cast [pauli_eq_prod, piKronecker_trace, pauli_trace']
    simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    push_cast [pauli_eq_prod, piKronecker_trace, h, reduceIte]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp [hi]

theorem pauli_apply (p q : Fin n → ℤ) (x : Register n) :
    (Pauli p q) • δ[x] = (I ^ (p ⬝ᵥ q + 2 * p ⬝ᵥ ↑x)) • δ[(x + ↑q)] := by
  calc
  _ = (τ ^ (p ⬝ᵥ q) • (XX q * ZZ p)) • δ[x] := by rw [pauli_def]
  _ = (τ ^ (p ⬝ᵥ q) • (XX q)) • ZZ p • δ[x] := by simp_rw [← smul_eq_mul, ← smul_assoc]
  _ = (τ ^ (p ⬝ᵥ q) • XX q) • (-1 : ℂ) ^ (p ⬝ᵥ ↑x) • δ[x] := by rw [ZZ_apply]
  _ = τ ^ (p ⬝ᵥ q) • (-1 : ℂ) ^ (p ⬝ᵥ ↑x) • XX q • δ[x] := by rw [smul_assoc]; nth_rw 2 [smul_comm]
  _ = (τ ^ (p ⬝ᵥ q) • (-1 : ℂ) ^ (p ⬝ᵥ ↑x)) • δ[(x + ↑q)] := by rw [XX_apply, ← smul_assoc]
  _ = (I ^ (p ⬝ᵥ q) • (-1 : ℂ) ^ (p ⬝ᵥ ↑x)) • δ[(x + ↑q)] := by
    rw [Submonoid.smul_def]; push_cast; simp [τ, u_I_eq_I]
  _ = (I ^ (p ⬝ᵥ q + 2 * p ⬝ᵥ ↑x)) • δ[(x + ↑q)] := by
    rw [← I_zpow_two, smul_eq_mul, ← _root_.zpow_mul, ← (_root_.zpow_add₀ Complex.I_ne_zero)]
