example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (h.right)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact h.left
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact h.left
      . exact hr
  exact fun h => ⟨Or.elim h (And.left) (And.left), Or.elim h (Or.inl ∘ And.right) (Or.inr ∘ And.right)⟩



example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro
  | ⟨w, Or.inl h⟩ => exact ⟨w, Or.inr h⟩
  | ⟨w, Or.inr h⟩ => exact ⟨w, Or.inl h⟩

-- example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
--   intros
--   sorry

#check Eq.trans

-- breaks
-- example (x y z w q : Nat) (h₁ : x = y) (h₅: x = q) (h₂ : y = z) (h₃ : z = w) : x = w := by
--   apply Eq.trans
--   assumption      -- solves x = ?b with h₁
--   apply Eq.trans
--   assumption      -- solves y = ?h₂.b with h₂
--   assumption      -- solves z = w with h₃

example : ∀ a b c : Nat, a=b → a=c → b=c := by -- unhygienic
  intros
  apply Eq.trans
  apply Eq.symm
  assumption
  assumption

example (x y : Nat) (h : x = y) : y = x := by
  revert h
  intro h
  exact Eq.symm h
  -- revert h
  -- -- goal is x y : Nat ⊢ x = y → y = x
  -- intro h₁
  -- -- goal is x y : Nat, h₁ : x = y ⊢ y = x
  -- apply Eq.symm
  -- assumption

example : 2 + 3 = 5 := by
  generalize 3 = x
  -- goal is x : Nat ⊢ 2 + x = 5
  admit

example (p q: Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => exact Or.inr hp
  | inr hq => exact Or.inl hq

example (p : Prop) : p ∨ p → p := by
  intro h
  cases h <;> assumption


def swap_pair : α × β → β × α := by
  intro p
  cases p
  constructor <;> assumption

example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h
  contradiction


def f (x y z : Nat) : Nat :=
  match x, y, z with
  | 5, _, _ => y
  | _, 5, _ => y
  | _, _, 5 => y
  | _, _, _ => 1

example (x y z : Nat) : x ≠ 5 → y ≠ 5 → z ≠ 5 → z = w → f x y w = 1 := by
  intros
  simp [f]
  split
  . contradiction
  . contradiction
  . contradiction
  . rfl

def g (xs ys : List Nat) : Nat :=
  match xs, ys with
  | [a, b], _ => a+b+1
  | _, [b, c] => b+1
  | _, _      => 1

#eval g [44,3,3] [2,3]

example (xs ys : List Nat) (h : g xs ys = 0) : False := by
  simp [g] at h; split at h <;> simp_arith at h
