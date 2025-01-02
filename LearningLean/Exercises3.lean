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


-- Exercises from chapter 4 proved with tactics

variable (α : Type) (p q : α → Prop)
variable (r : Prop)


example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  apply Iff.intro
  . intro h
    apply And.intro <;> intro x <;> have pq := h x
    exact pq.left; exact pq.right
  . intro h
    intro x
    have hp := h.left x; have hq := h.right x
    apply And.intro <;> assumption

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h₁ h₂
  intro x
  exact (h₁ x) (h₂ x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h x
  cases h with
  | inl hl => apply Or.inl; apply hl;
  | inr hr => apply Or.inr; apply hr;

example : α → ((∀ x : α, r) ↔ r) := by
  intro x
  apply Iff.intro
  . intro h
    apply h; assumption
  . intro hr x2
    assumption

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  apply Iff.intro
  . intro h
    cases (em r) with
    | inl hr => apply Or.inr; assumption
    | inr hnr => apply Or.inl; intro x; cases h x with
      | inl ht => assumption
      | inr hf => exact absurd hf hnr
  . intro h x
    cases h with
    | inl ht => apply Or.inl; exact ht x
    | inr hf => apply Or.inr; assumption

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  apply Iff.intro
  . intro h hr x
    exact (h x) hr
  . intro h x hr
    exact (h hr) x

section BarberShop

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have problem := h barber
  have doesNotShaveHimself := fun x => (problem.mp x) x
  have doesShaveHimself := problem.mpr doesNotShaveHimself
  exact absurd doesShaveHimself doesNotShaveHimself

end BarberShop

example : (∃ x : α, r) → r := by
  intro h
  match h with
  | ⟨x, hx⟩ => assumption

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  apply Exists.intro
  assumption; assumption

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨x, hx⟩ => apply And.intro; apply Exists.intro x; exact hx.left; exact hx.right
  . intro h
    match h.left with
    | ⟨x, hx⟩ => apply Exists.intro x; apply And.intro; repeat assumption; exact h.right


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  . intro h
    match h with
    | ⟨x, hx⟩ => cases hx; apply Or.inl; apply Exists.intro x; assumption;
                  apply Or.inr; apply Exists.intro x; assumption
  . intro h
    cases h with
    | inl hl => match hl with
      | ⟨x, hx⟩ => apply Exists.intro x; apply Or.inl; assumption
    | inr hr => match hr with
      | ⟨x, hx⟩ => apply Exists.intro x; apply Or.inr; assumption

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    intro nh
    match nh with
    | ⟨x, hx⟩ => exact hx (h x)
  . intro h
    intro x
    cases (em (p x)) with
    | inl hpx => assumption
    | inr nhpx => apply False.elim; exact h ⟨x, nhpx⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  apply Iff.intro
  intro h hn
  match h with
  | ⟨x, hx⟩ => exact (hn x) hx
  intro h
  apply byContradiction
  intro nh
  apply h
  intro x
  intro h2
  exact nh (by apply Exists.intro x; assumption)

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    intro x
    intro hpx
    apply h
    apply Exists.intro x
    assumption
  . intro h
    intro he
    match he with
    | ⟨x, hx⟩ => exact (h x) hx

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  apply Iff.intro
  . intro h
    apply byContradiction
    intro nh
    apply h
    intro x
    cases (em (p x)) with
    | inl hpx => assumption
    | inr hnpx => exact False.elim (nh (by apply Exists.intro x; exact hnpx))
  . intro h
    intro nh
    match h with
    | ⟨x, hx⟩ => exact hx (nh x)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  apply Iff.intro
  . intro h
    intro h2
    match h2 with
    | ⟨x, hx⟩ => exact (h x) hx
  . intro h
    intro x
    intro hpx
    exact h (by apply Exists.intro x; assumption)

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  apply Iff.intro
  . intro h
    intro h2
    match h with
    | ⟨x, hx⟩ => apply hx; exact h2 x
  . intro h
    cases (em (∀ x, p x)) with
    | inl hallpx => apply Exists.intro a; intro _; exact h hallpx
    | inr hnallpx =>
    have w : (∃ (x:α), ¬ p x):= (by
    apply byContradiction;
    intro nh; apply hnallpx; intro x; cases (em (p x)); assumption;
    apply False.elim; exact nh (by apply Exists.intro x; assumption))
    match w with
    | ⟨x, hx⟩ => apply Exists.intro x; intro hpx; exact absurd hpx hx

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  apply Iff.intro
  . intro h hr
    match h with
    | ⟨x, hx⟩ => apply Exists.intro x; exact hx hr
  . intro h
    cases (em r) with
    | inl hr => match h hr with
      | ⟨x, hx⟩ => apply Exists.intro x; intro _; assumption
    | inr hnr => apply Exists.intro a; intro hr; exact absurd hr hnr


-- Ex 2 : One line proof question

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  constructor <;> (try constructor) <;> repeat (first | apply Or.inl; assumption | apply Or.inr | assumption)
