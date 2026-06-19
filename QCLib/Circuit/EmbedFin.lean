module

public import QCLib.Circuit.Embed
public import QCLib.Logic.Equiv

/-! TODO  -/

@[expose] public section

open Matrix UnitaryGroup Equiv

variable {n m d : ℕ} (h : n ≤ m)

@[simps! coe]
def embedFin (U : 𝐔[Fin n → Fin d]) : 𝐔[Fin m → Fin d] :=
  subtype (fun i : Fin m ↦ i.val < n)
    (reindexMonoidEquiv (finFunSubtypeEquiv d h) U)

@[simps! -isSimp apply]
def embedFinHom : 𝐔[Fin n → Fin d] →* 𝐔[Fin m → Fin d] :=
  MonoidHom.mk' (embedFin h) (fun a b ↦ by ext; simp [embedFin, ← blockDiagonal_mul])

@[simp]
theorem embedFinHom_map_self (U : 𝐔[Fin n → Fin d]) : embedFinHom (le_refl n) U = U := by
  ext
  simp [embedFinHom_apply, blockDiagonal_apply, funext_iff, finFunSubtypeEquiv, piCongrLeft']

@[simp]
theorem embedFinHom_trans {k} (U : 𝐔[Fin n → Fin d]) (hn : n ≤ k) (hk : k ≤ m) :
    embedFinHom hk (embedFinHom hn U) = embedFinHom (le_trans hn hk) U := by
  ext a b
  simp [embedFinHom, blockDiagonal_apply, funext_iff, finFunSubtypeEquiv, piCongrLeft']
  split_ifs with h1 h2 h3 <;> try grind
  obtain ⟨q, hq⟩ := not_forall.mp h3
  by_cases hkq : k ≤ q
  · have := h1 q
    simp_all
  · simp only [not_le] at hkq
    have := h2 ⟨q, hkq⟩
    exfalso
    exact hq (by simp_all)

@[simp]
theorem embedFinHom_single_castAdd (k) (i : Fin n) (U : 𝐔[Fin d]) :
    embedFinHom le_self_add (single i U) = single (i.castAdd k) U := by
  ext i j
  simp [embedFinHom, blockDiagonal_apply, funext_iff, ← ite_and]
  split_ifs with h1 h2 <;> try grind
  exfalso
  have ⟨x, hx⟩ := not_forall.mp h2
  by_cases hnx : n ≤ x
  · have := h1.1 x hnx
    simp_all
  · have := h1.2 ⟨x, by lia⟩ (by grind)
    simp_all

@[simp]
theorem embedFinHom_single_castSucc (i : Fin n) (U : 𝐔[Fin d]) :
    embedFinHom (Nat.le_succ n) (single i U) = single i.castSucc U := by
  simp [Fin.castSucc]

@[simp]
theorem embedFinHom_diagonalMonoidHom_castAdd (k : ℕ) (f : (Fin n → Fin d) → (unitary ℂ)) :
    embedFinHom le_self_add (diagonalMonoidHom f)
      = diagonalMonoidHom
          (fun y : Fin (n + k) → Fin d ↦ f (fun i ↦ y (i.castAdd k))) := by
  ext i j
  simp [embedFinHom, diagonal_apply, funext_iff]
  split_ifs with h1 h2 <;> try grind
  rfl

@[simp]
theorem embedFinHom_diagonalMonoidHom_castSucc (f : (Fin n → Fin d) → (unitary ℂ)) :
    embedFinHom (Nat.le_succ n) (diagonalMonoidHom f) =
      diagonalMonoidHom (fun y : Fin (n + 1) → Fin d ↦ f (fun i ↦ y i.castSucc)) := by
  simp [Fin.castSucc]
