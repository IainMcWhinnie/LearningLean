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


example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  . intro h
    apply And.intro
    intro hp
    exact h (Or.inl hp)
    intro hq
    exact h (Or.inr hq)
  . intro h
    intro hpq
    cases hpq with
    | inl hp => exact h.left hp
    | inr hq => exact h.right hq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h
  intro hpq
  cases h with
  | inl hp => exact hp hpq.left
  | inr hq => exact hq hpq.right


example : ¬(p ∧ ¬p) := by
  intro hem
  exact hem.right hem.left

example : p ∧ ¬q → ¬(p → q) := by
  intro h
  intro hpq
  have hq : q := by exact hpq h.left
  exact h.right hq

example : ¬p → (p → q) := by
  intro hnp hp
  exact absurd hp hnp

example : (¬p ∨ q) → (p → q) := by
  intro hpq hp
  cases hpq
  exact absurd hp (by assumption)
  assumption

example : p ∨ False ↔ p := by
  apply Iff.intro
  . intro h
    cases h with
    | inl hp => exact hp
    | inr hf => exact False.elim hf
  . intro h
    apply Or.inl
    assumption

example : p ∧ False ↔ False := by
  apply Iff.intro
  . intro h
    exact h.right
  . intro h
    apply And.intro
    exact False.elim h
    assumption

example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  have hq : q := by exact hpq hp
  exact hnq hq

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  cases (em p) with
  | inr hnp => apply Or.inl; intro hp; exact absurd hp hnp
  | inl hp => match (h hp) with
    | Or.inl hq => apply Or.inl; intro _; assumption
    | Or.inr hr => apply Or.inr; intro _; assumption

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  cases (em p) with
  | inl hp => apply Or.inr; intro hq; exact h ⟨hp, hq⟩
  | inr hnp => apply Or.inl; assumption

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  cases (em p) with
  | inl hp => apply And.intro; assumption; cases (em q) with
    | inl hq => apply False.elim; apply h; intros; assumption
    | inr hnq => assumption
  | inr hnp => cases (em q) with
    | inl hq => apply False.elim; apply h; intros; assumption
    | inr hnq => apply False.elim; apply h; intro hp; exact absurd hp hnp

example : (p → q) → (¬p ∨ q) := by
  intro h
  cases (em p) with
  | inr hnp => apply Or.inl; assumption
  | inl hp => apply Or.inr; exact h hp

example : (¬q → ¬p) → (p → q) := by
  intro h hp
  cases (em q) with
  | inl hq => assumption
  | inr hnq => exact absurd hp (h hnq)

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) := by
  intro h
  cases (em p) with
  | inl hp => assumption
  | inr hnp => apply h; intro hp; exact absurd hp hnp

example : ¬(p ↔ ¬p) := by
  intro h
  have hnp := fun x => (h.mp x) x
  have hp := h.mpr hnp
  apply hnp
  assumption
