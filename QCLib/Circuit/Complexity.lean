/-
Copyright (c) 2026 David Gross, Davood Tehrani. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Gross, Davood Tehrani
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.Order.CompleteLattice.Lemmas
public import Mathlib.Order.CompleteLattice.Group
public import QCLib.Mathlib.Lemmas
public import QCLib.Circuit.Embed

/-!

# Experimental file

Incomplete and experimental. Currently stated only for `n` qubit circuits with `n > 1`.

--

The aim of this file is establish a framework for talking about circuit complexity measures.

The circuit complexity of a unitary can be measured in various ways: The minimal
number of two-qubit gates required to produce it / the minimal depth of a
circuit / number of non-Clifford gates / in terms of a precise or approximate
realization...

All natural complexity measures are subadditive, in that `f (a * b) ≤ f a + f b`.
This behavior is captured by the Mathlib typeclass `MulLEAddHomClass`. There is
also `GroupSeminormClass`, which adds the assumptions `f 1 = 0` (sensible for
complexity measures) and `f a⁻¹ = f a` (which is not necessarily true for gate
sets that aren't closed under taking inverses).

There is not too much API provided for these classes. Still, we build on them.

For now, we work with `GroupSeminormClass`, though relaxing that is TBD.



Define the complexity of a unitary in terms of the number of two-qubit gates required to express it.

This should be generalized to `k`-local gates. (In particular, the definitions
don't work for `n=1`. While the case is not interesting from a
complexity-theoretic perspective, it's a bit inelegant not covering it).

## Main Definitions

* `GateComplexityFun₂ : 𝐔[Register n] → ℕ∞`: Minimal number of two-qubit gates
required to express a unitary.

## Main Results

* A bundled version of `GateComplexityFun₂` is an instance of `GroupSeminormClass`

## TODO

* Define more complexity measures.

* Every unitary has  finite complexity in terms of two-qubit gates. See, e.g.  https://arxiv.org/pdf/quant-ph/9503016. It would be very nice to a have a formalized proof of this result.

* Actually apply the lemmas in the `GroupSeminorm` section to concrete unitaries.

-/

@[expose] public section

/- Lemmas on functions that are subadditive in the sense that `f (a * b) ≤ f a + f b` -/
-- TBD: Can probably weaken assumptions to `MulLEAddHomClass` with `h : f 1 = 0`.
section GroupSeminorm

variable {F α β ι : Type*}

variable [Group α]
variable [AddCommMonoid β] [PartialOrder β] [AddLeftMono β]
variable [FunLike F α β] [GroupSeminormClass F α β]

theorem List.map_prod_le_sum (f : F) (l : List α) : (f l.prod) ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l hi =>
    simp only [prod_cons, map_cons, sum_cons]
    grw [map_mul_le_add, hi]

-- TBD: Multiset version
theorem Finset.map_noncommProd_le_sum (f : F) {γ : Type*} (s : Finset γ) (g : γ → α) (comm) :
    (f (s.noncommProd g comm)) ≤ ∑ a ∈ s, f (g a) := by
  rw [← noncommprod_map_toList, ← sum_map_toList]
  grw [List.map_prod_le_sum]
  simp


-- `GroupSeminormClass` is stated for `FunLike` types, not for functions
-- directly. To use it, introduce the `ComplexityMeasure` structure. (Feels a
-- bit overformalized? Lots of boilerplate. TBD: Simplify?)

variable (α β)

-- TBD: Unbundle `map_inv_eq_map`.
/-- Type of complexity measures. Mostly boilerplate because `GroupSeminormClass`
wants a `FunLike` type. -/
structure ComplexityMeasure where
  toFun : α → β
  map_one_eq_zero : toFun 1 = 0
  map_mul_le_add : ∀ a b, toFun (a * b) ≤ toFun a + toFun b
  map_inv_eq_map : ∀ a, toFun a⁻¹ = toFun a

instance : FunLike (ComplexityMeasure α β) α β where
  coe f := f.toFun
  coe_injective' f g h := by cases f; cases g; congr

instance : GroupSeminormClass (ComplexityMeasure α β) α β where
  map_one_eq_zero f := f.map_one_eq_zero
  map_mul_le_add f := f.map_mul_le_add
  map_inv_eq_map f := f.map_inv_eq_map

end GroupSeminorm

open Matrix Matrix.UnitaryGroup Qubit

public section

-- Currently, we only talk about two-qubit gates. This means in particular that
-- non-trivial single-qubit circuits formally have complexity `∞`. TBD:
-- Generalize to `k`-local gates.

/-- Structure that bundles the information where and how a two-qubit gate acts. -/
structure TwoQubitGate (n : ℕ) where
  i : Fin n
  j : Fin n
  hneq : i ≠ j
  U : 𝐔[Qubit × Qubit]

/-- A circuit is a list of two qubit gates -/
abbrev Circuit (n : ℕ) := List (TwoQubitGate n)

variable {n : ℕ}

/-- The unitary realizing the two-qubit gate. -/
@[simp]
noncomputable def TwoQubitGate.Unitary (g : TwoQubitGate n) : 𝐔[Register n] :=
  bipartiteMonoidHom' g.i g.j g.hneq g.U

/--
The set of all circuit decompositions of a unitary.
-/
def Circuits (U : 𝐔[Register n]) : Set (Circuit n) :=
  { L : Circuit n | (L.map TwoQubitGate.Unitary).prod = U }

@[simp]
theorem elem_circuits_iff {L : Circuit n} {U : 𝐔[Register n]} :
    (L ∈ Circuits U) ↔ (L.map TwoQubitGate.Unitary).prod = U := by
  rfl

@[simp]
def TwoQubitGate.inv (g : TwoQubitGate n) : TwoQubitGate n := {g with U := g.U⁻¹}

@[simp]
theorem twoQubitGate_unitary_comp_inv : TwoQubitGate.Unitary ∘ TwoQubitGate.inv =
    (fun U : 𝐔[Register n] ↦ U⁻¹) ∘ TwoQubitGate.Unitary := by ext; simp

@[simp]
theorem twoQubitGate_inv_inv : TwoQubitGate.inv ∘ TwoQubitGate.inv = @id (TwoQubitGate n) :=
  by ext; simp

example (g : TwoQubitGate n) : g.inv.Unitary = (g.Unitary)⁻¹ := by simp

@[simp]
theorem nil_elem_circuits_one : [] ∈ Circuits (1 : 𝐔[Register n]) := by
  simp

@[simp]
theorem self_elem_circuits_biparite {i j : Fin n} (h : i ≠ j) (U : 𝐔[Qubit × Qubit]) :
    [⟨i, j, h, U⟩] ∈ Circuits (bipartite i j U h) := by
  simp [bipartiteMonoidHom_apply]

theorem circuit_rev_inv (U : 𝐔[Register n]) : ∀ (L : Circuit n),
    (L ∈ Circuits U) → ((L.reverse.map TwoQubitGate.inv) ∈ Circuits U⁻¹) := fun L hL ↦ by
  simp [(congrArg (·⁻¹) hL).symm, List.prod_inv_reverse]

@[simp]
theorem circuit_rev_inv_iff {U : 𝐔[Register n]} : ∀ (L : Circuit n),
    (L ∈ Circuits U) ↔ ((L.reverse.map TwoQubitGate.inv) ∈ Circuits U⁻¹) := fun L ↦
      ⟨circuit_rev_inv U L, by simpa using circuit_rev_inv U⁻¹ (L.reverse.map TwoQubitGate.inv)⟩

open ENat

-- This functional actually attains only finite values, though this isn't proven.
/-- The minimal length of a circuit decomposition of `U` in terms of two-qubit gates -/
noncomputable def GateComplexityFun₂ (U : 𝐔[Register n]) : ℕ∞ :=
  sInf ((fun L ↦ L.length) '' (Circuits U))

theorem GateComplexityFun₂_apply (U : 𝐔[Register n]) :
    GateComplexityFun₂ U = ((sInf ((fun L ↦ L.length) '' (Circuits U))) : ℕ∞) := rfl

-- Why does `ENat.sInf_eq_zero` not have `@simp` (unlike `Nat` version?)
theorem gateComplexity₂_one : GateComplexityFun₂ (1 : 𝐔[Register n]) = 0 := by
  simp [GateComplexityFun₂, sInf_eq_zero]

@[simp]
theorem gateComplexity₂_le (U : 𝐔[Register n]) (L : Circuit n) (h : L ∈ Circuits U) :
    GateComplexityFun₂ U ≤ L.length := sInf_le (by grind)

@[simp]
theorem exists_circuit_of_ne_top {U : 𝐔[Register n]} (h : GateComplexityFun₂ U ≠ ⊤) :
    ∃ L ∈ Circuits U, GateComplexityFun₂ U = L.length := by
  have h2 : (((fun L ↦ L.length) '' Circuits U) : Set ℕ∞).Nonempty := by
    contrapose! h
    simp_all [GateComplexityFun₂_apply]
  simp only [GateComplexityFun₂]
  grind [csInf_mem h2]

theorem gateComplexity₂_mul (U V : 𝐔[Register n]) :
    GateComplexityFun₂ (U * V) ≤ GateComplexityFun₂ U + GateComplexityFun₂ V := by
  by_cases h : GateComplexityFun₂ U = ⊤ ∨ GateComplexityFun₂ V = ⊤
  · cases h <;> grind [top_add, add_top, le_top]
  · push Not at h
    obtain ⟨lU, hUelem, hUlen⟩ := exists_circuit_of_ne_top h.1
    obtain ⟨lV, hVelem, hVlen⟩ := exists_circuit_of_ne_top h.2
    grw [gateComplexity₂_le (U * V) (lU ++ lV)] <;> simp_all

lemma circuit_inv_aux {U : 𝐔[Register n]} (m : ℕ∞) (h : m ∈ (fun L ↦ L.length) '' (Circuits U)) :
    m ∈ (fun L ↦ L.length) '' (Circuits U⁻¹) := by
  simp_all only [Set.mem_image]
  obtain ⟨L, helem, hlen⟩ := h
  use L.reverse.map TwoQubitGate.inv
  exact ⟨(circuit_rev_inv_iff L).mp helem, by simp [hlen]⟩

theorem gateComplexity₂_inv (U : 𝐔[Register n]) :
    GateComplexityFun₂ U⁻¹ = GateComplexityFun₂ U := le_antisymm
      (sInf_le_sInf (by apply circuit_inv_aux))
      (sInf_le_sInf (by
        have := circuit_inv_aux (U := U⁻¹)
        simpa only [inv_inv])) -- `simpa using` doesn't work for some reason.

@[simps] -- TBD: Remove attribute
noncomputable def GateComplexity₂ : ComplexityMeasure 𝐔[Register n] ℕ∞ where
  toFun := GateComplexityFun₂
  map_one_eq_zero := gateComplexity₂_one
  map_mul_le_add := gateComplexity₂_mul
  map_inv_eq_map := gateComplexity₂_inv

@[simp]
theorem gateComplexity₂_bipartite_le {i j : Fin n} (h : i ≠ j) (U : 𝐔[Qubit × Qubit]) :
    GateComplexity₂ (bipartite i j U h) ≤ 1 := by
  grw [GateComplexity₂_toFun,
    gateComplexity₂_le (bipartite i j U h) [⟨i, j, h, U⟩] (self_elem_circuits_biparite h U)]
  simp

end
