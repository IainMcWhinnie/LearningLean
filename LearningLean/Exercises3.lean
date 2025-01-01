variable (p q r : Prop)

-- Exercises from chapter 3 proved with tactics

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro
    | And.intro hp hq => apply And.intro; exact hq; exact hp
  . intro
    | And.intro hq hp => apply And.intro; exact hp; exact hq

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hp => apply Or.inr; assumption
    | inr hq => apply Or.inl; assumption
  . intro h
    cases h with
    | inl hq => apply Or.inr; assumption
    | inr hp => apply Or.inl; assumption


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro h
    apply And.intro
    exact h.left.left
    apply And.intro
    exact h.left.right
    exact h.right
  . intro h
    apply And.intro
    apply And.intro
    exact h.left
    exact h.right.left
    exact h.right.right

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    match h with
    | Or.inl (Or.inl hp) => apply Or.inl; assumption
    | Or.inl (Or.inr hq) => apply Or.inr; apply Or.inl; assumption
    | Or.inr hr => apply Or.inr; apply Or.inr; assumption
  . intro h
    match h with
    | Or.inl hp => apply Or.inl; apply Or.inl; assumption
    | Or.inr (Or.inl hq) => apply Or.inl; apply Or.inr; assumption
    | Or.inr (Or.inr hr) => apply Or.inr; assumption

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    match h.right with
    | Or.inl hq => apply Or.inl; apply And.intro; exact h.left; assumption
    | Or.inr hr => apply Or.inr; apply And.intro; exact h.left; assumption
  . intro h
    match h with
    | Or.inl hpq => apply And.intro; exact hpq.left; apply Or.inl; exact hpq.right
    | Or.inr hpr => apply And.intro; exact hpr.left; apply Or.inr; exact hpr.right

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro h
    match h with
    | Or.inl hp => apply And.intro; apply Or.inl; assumption; apply Or.inl; assumption
    | Or.inr hqr => apply And.intro; apply Or.inr; exact hqr.left; apply Or.inr; exact hqr.right
  . intro h
    match h.left with
    | Or.inl hp => apply Or.inl; assumption
    | Or.inr hq => match h.right with
      | Or.inl hp => apply Or.inl; assumption
      | Or.inr hr => apply Or.inr; apply And.intro; repeat assumption

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intro h
    intro ⟨hp, hq⟩
    exact h hp hq
  . intro h hp hq
    have hpq : p ∧ q := by apply And.intro; repeat assumption
    exact h hpq

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    apply And.intro
    intro hp
    apply h
    apply Or.inl
    assumption
    intro hq
    apply h
    apply Or.inr
    assumption
  . intro h
    intro hpq
    match hpq with
    | Or.inl hp => apply h.left; assumption
    | Or.inr hq => apply h.right; assumption


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry

example : ¬(p ↔ ¬p) := sorry
