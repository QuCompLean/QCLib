import Qml.AssocRw
import Mathlib

variable
  (G : Type) [Semigroup G]
  (X Y s : G)
  (h1 : s * X * Y = Y * X)
  (h2 : s * X = X * s)
set_option linter.unusedVariables false

-- basic substitution
example (a b c : ℕ) (h : a * b = c) : a * b * a = c * a := by
  assoc_rw [h]
-- chained rewrites
example (a b c d : G) (h1 : a * b = c) (h2 : c * a = d) :
    a * b * a = d := by
  assoc_rw [h1, h2]
-- ← rewrite using symm chain, check if metadata drop works
example : X * Y * X = s * (X * X) * Y := by
  have h_symmw := h1.symm
  assoc_rw [← h_symmw.symm, h2.symm]

-- check wether ← is processed properly
example : X * Y * X = s * (X * X) * Y := by
  assoc_rw [← h1, ← h2]

-- rewrite under function application
example (f : G → G) : f (s * X * Y) * s = f (Y * X) * s := by
  assoc_rw [h1]


-- substitution right of *
example (a b c d : ℕ) (h : a * b = c) : d * (a * b) = d * c := by
  assoc_rw [h]


-- rewrite at hypothesis
example (a b c d : G) (h1 : a * b = c) (h2 : a * b * d = c * d) :
    c * d = c * d := by
  assoc_rw [h1] at h2

-- universal hypothesis
example (a b c : G) (h : ∀ x : G, x * a = a * x) :
    b * a * c = a * b * c := by
  assoc_rw [h b]

-- rewrite inside nested product
example (a b c d : G) (h : b * c = d) :
    a * (b * c) * a = a * d * a := by
  assoc_rw [h]

-- two-step chained rewrite
example (a b c d : G) (h1 : a * b = c) (h2 : c * b = d) :
    a * b * b = d := by
  assoc_rw [h1, h2]




-- rewrite at single hyp vs at *
example (a b c : Nat) (h : a + b = c) (h2 : a + b + c = c + c) :
    c + c = c + c := by
  assoc_rw [h] at h2

example (a b c : Nat) (h : a + b = c) (h2 : a + b + c = c + c) :
    a + b + c = c + c := by
  assoc_rw [h] at *

-- Nat mul
example (a b c : Nat) (h : a * b = c) : a * b * c = c * c := by
  assoc_rw [h]

-- iterate: multiple occurrences
example (a b c d e f : Nat) (h : a + b = c) :
    a + b + a + b + a + b + d = c + c + c + d := by
  iterate assoc_rw [h]

example (a b c : Nat) (h : a + b = c) :
    a + b + (a + b) = c + c := by
  iterate assoc_rw [h]

example (a b c d e : Nat) (h1 : a + b = c) (h2 : c + d = e) :
    a + b + d = e := by
  assoc_rw [h1, h2]

example (a b c d : Nat) (h1 : a + b = c) (h2 : a + b + c + d = c + c + d) :
    c + c + d = c + c + d := by
  assoc_rw [h1] at h2

-- rewrite at all goals
example (a b c d : Nat) (h : a + b = c)
    (h2 : a + b + d = c + d)
    (h3 : a + b + a + b = c + c) :
    c + d = c + d := by
  assoc_rw [h] at *

-- rewrite in reverse (rhs → lhs)
example (a b c d : ℕ) (h : a * b = c) : d * c = d * (a * b) := by
  assoc_rw [h]

-- rewrite inside Prop hypothesis
example (a b c : ℕ) (h : a * b = c) (f : ℕ → Prop) (hin : f (a * b * a)) :
    f (c * a) := by
  assoc_rw [h] at hin
  assumption

-- rewrite under function
example (a b c : G) (f : G → G) (h : a * b = c) :
    f (a * b * c) = f (c * c) := by
  assoc_rw [h]

example (a b c : G) (f : G → G) (h : a * b = c)
    (hyp : f (a * b * c) = f c) : f (c * c) = f c := by
  assoc_rw [h] at hyp
  exact hyp

example (a b c : G) (f : G → G) (h : a * b = c) :
    f (a * b) * c = f c * c := by
  assoc_rw [h]

-- custom op via def
def myMul (a b : ℕ) := a * b
instance : Std.Associative myMul := ⟨fun a b c => by simp [myMul, Nat.mul_assoc]⟩

example (a b c : ℕ) (h : myMul a b = c) : myMul (myMul a b) c = myMul c c := by
  assoc_rw [h]


-- universal commutativity
example (a b c d : G) (h : ∀ x y : G, x * y = y * x) :
    a * b * c = b * a * c := by
  assoc_rw [h a b]

-- rewrite inside forall goal
example (a b c e f : G) (h : a * b = c) :
    (∀ d : G, a * b * d * (e * f) = c * d * (e * f)) ↔ True := by
  assoc_rw [h]
  simp

-- rewrite inside nested parens
example (a b c e f : G) (h : b * c = d) :
    a * (b * (c * d)) = a * (d * d) := by
  assoc_rw [h]

-- test non numbers
example (xs ys zs ws : List Nat) (h : xs ++ ys = ws) :
    xs ++ ys ++ zs = ws ++ zs := by
  assoc_rw [h]

-- test non equallities
-- these do not close with just ac_rfl but rfl closes it (also ac_nf closes them)
example (α : Type) [Semigroup α] (a b c d : α) (s : Set α) (h : a * b = c) :
    (a * b * c) * d ∈ s ↔ (c * c) * d ∈ s := by
  assoc_rw [h]


example (α : Type) [Semigroup α] [Preorder α] [CovariantClass α α (· * ·) (· ≤ ·)]
    (a b c d : α) (h : a * b = c) :
    a * b * d ≤ c * d := by
  assoc_rw [h]

--  ∣ in a monoid
example (α : Type) [Monoid α] (a b c d : α) (h : a * b = c) :
    c * d ∣ a * b * d := by
  assoc_rw [h]
-- left conjunct
example (α : Type) [Semigroup α] (a b c d : α) (h : a * b = c) (P : α → Prop) :
    P (a * b * d) ∧ True ↔ P (c * d) ∧ True := by
  assoc_rw [h]


--  ∨ right disjunct
example (α : Type) [Semigroup α] (a b c d : α) (h : a * b = c) (P Q : α → Prop) :
    P (c * d) ∨ Q (a * b * d) ↔ P (c * d) ∨ Q (c * d) := by
  assoc_rw [h]


-- generic f with Std.Associative
example {α : Type*} (f : α → α → α) [Std.Associative f] (a b c d x : α) :
    f b c = x → f (f (f a b) c) d = f (f a x) d := by
  intro h
  assoc_rw [h]

-- double rewrite same hyp
example (a b c d : ℕ) (h : a * b = c) :
    (a * b) * (a * b) = c * c := by
  assoc_rw [h, h]

-- iterate commutativity
example (a b : G) (h : ∀ x : G, a * x = x * a) :
    b * a * a = a * a * b := by
  iterate assoc_rw [← h]

example (a b c : G) (h : ∀ x : G, x * a = a * x) :
    b * c * a * c = b * (a * c) * c := by
  iterate assoc_rw [h]

-- rewrite using ← in hyp
example (a b c d e : ℕ) (h : c * c = a + b) (hyp : c * c + d + e = c * c + d) :
    a + b + d + e = c * c + d := by
  assoc_rw [← h]
  exact hyp

-- multiple different ops in same goal
example (a b c d e f : ℕ) (h1 : a * b = c) (h2 : d + e = f) (h3 : a * b + (d + e) = c + f) :
    a * b + (d + e) = c + f := by
  assoc_rw [h1, h2] at h3
  assoc_rw [h1, h2]

-- custom op via def (addition)
def assocOp (a b : Nat) : Nat := a + b
instance : Std.Associative assocOp := ⟨fun a b c => by simp [assocOp, Nat.add_assoc]⟩

example (a b c : Nat) (h : assocOp a b = c) : assocOp (assocOp a b) c = assocOp c c := by
  assoc_rw [h]

-- Std.Associative passed explicitly
example (α : Type) (op : α → α → α) (h_assoc : Std.Associative op)
    (a b c d : α) (h : op a b = c) :
    op (op a b) d = op c d := by
  assoc_rw [h]


-- lambda op
example (a b c d : ℕ) (h : (fun x y => x + y) a b = c) :
    (fun x y => x + y) ((fun x y => x + y) a b) d =
    (fun x y => x + y) c d := by
  assoc_rw [h]

-- MyAlg structure: three spellings of associativity witness
structure MyAlg (α : Type*) where
  op : α → α → α
  assoc : Std.Associative op

example (α : Type*) (s : MyAlg α) (a b c d : α)
    (h : s.op a b = c) :
    s.op (s.op a b) d = s.op c d := by
  have : Std.Associative s.op := s.assoc
  assoc_rw [h]

example (α : Type*) (s : MyAlg α) (a b c d : α) (hs : Std.Associative s.op := s.assoc)
    (h : s.op a b = c) :
    s.op (s.op a b) d = s.op c d := by
  assoc_rw [h]

example (α : Type*) (s : MyAlg α) (a b c d : α)
    (h : s.op a b = c) :
    s.op (s.op a b) d = s.op c d := by
  have h_hyp : Std.Associative s.op := s.assoc
  assoc_rw [h]

variable {α : Type} (op : α → α → α) [Std.Associative op]
local infixl:70 " ⋆ " => op

-- List Int with omega
example (a b c d e f g x : List Int) (h : c ++ d ++ e ++ f = x)
    (P : List Int → Prop) (hp : P ((a ++ (b ++ x)) ++ g)) :
    P ((a ++ (b ++ (c ++ d))) ++ ((e ++ f) ++ g)) := by
  assoc_rw [h]
  omega

variable {α : Type} [Mul α] [Std.Associative (α := α) (· * ·)]

-- assoc_rw: left-grouped result
example (a b c d e f g x : α) (h : c * d * e * f = x) (P : α → Prop)
    (hp : P ((a * (b * x)) * g)) :
    P ((a * (b * (c * d))) * ((e * f) * g)) := by
  assoc_rw [h]
  exact hp

-- longer left-grouped
example (a b c d e f g h i j x : α) (h_eq : d * e * f * g * h = x)
    (P : α → Prop)
    (hp : P ((a * (b * (c * x))) * (i * j))) :
    P ((a * (b * (c * (d * e)))) * ((f * g) * (h * (i * j)))) := by
  assoc_rw [h_eq]
  exact hp

-- rewrite at hyp (reverse direction)
example (a b c d e f g h i j x : α) (h_eq : d * e * f * g * h = x)
    (P : α → Prop)
    (hyp : P ((a * (b * (c * (d * e)))) * ((f * g) * (h * (i * j))))) :
    P ((a * (b * (c * x))) * (i * j)) := by
  assoc_rw [h_eq] at hyp
  exact hyp

-- ssoc_rw_right produces different grouping than assoc_rw

-- Gold example: same goal, different hp shape
-- assoc_rw needs  hp : P ((a * x) * e)
-- assoc_rw_right needs hp : P (a * (x * e))
example (a b c d e x : α) (h : b * c * d = x) (P : α → Prop)
    (hp : P ((a * x) * e)) :
    P ((a * b) * ((c * d) * e)) := by
  assoc_rw [h]; exact hp

example (a b c d e x : α) (h : b * c * d = x) (P : α → Prop)
    (hp : P (a * (x * e))) :
    P ((a * b) * ((c * d) * e)) := by
  assoc_rw_right [h]
  exact hp
--fail_if_succeeds -- fail_if_success
-- assoc_rw_right with longer h_eq
example (a b c d e f g h i j x : α) (h_eq : d * e * f * g * h = x)
    (P : α → Prop)
    (hp : P ((a * (b * c)) * (x * (i * j)))) :
    P ((a * (b * (c * (d * e)))) * ((f * g) * (h * (i * j)))) := by
  assoc_rw_right [h_eq]
  exact hp

-- pairs where assoc_rw and assoc_rw_right coincide
example (a b c d e x : α) (h : c * d * e = x) (P : α → Prop)
    (hp : P ((a * b) * x)) :
    P ((a * b) * ((c * d) * e)) := by
  assoc_rw [h]; exact hp

example (a b c d e x : α) (h : c * d * e = x) (P : α → Prop)
    (hp : P ((a * b) * x)) :
    P ((a * b) * ((c * d) * e)) := by
  assoc_rw_right [h]; exact hp

-- simple base cases
example (a b x : α) (h : a * b = x) (P : α → Prop) (hp : P x) :
    P (a * b) := by
  assoc_rw [h]; exact hp

example (a b c x : α) (h : a * b * c = x) (P : α → Prop) (hp : P x) :
    P ((a * b) * c) := by
  assoc_rw [h]; exact hp

-- c * d rewrite with trailing element
example (a b c d e x : α) (h : c * d = x) (P : α → Prop)
    (hp : P (a * (b * (x * e)))) :
    P (a * (b * (c * (d * e)))) := by
  assoc_rw [h]; exact hp

-- c * d rewrite with two trailing elements
example (a b c d e f x : α) (h : c * d = x) (P : α → Prop)
    (hp : P (a * (b * (x * (e * f))))) :
    P (a * (b * (c * (d * (e * f))))) := by
  assoc_rw [h]; exact hp

-- four-element h, one trailing
example (a b c d e f g x : α) (h : c * d * e * f = x) (P : α → Prop)
    (hp : P (a * (b * (x * g)))) :
    P (a * (b * (c * (d * (e * (f * g)))))) := by
  assoc_rw [h]; exact hp

example (a b c d e f g x : α) (h : c * d * e * f = x) (P : α → Prop)
    (hp : P (a * (b * (x * g)))) :
    P (a * (b * (c * (d * (e * (f * g)))))) := by
  assoc_rw_right [h]; exact hp
