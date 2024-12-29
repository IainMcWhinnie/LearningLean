variable (p q r : Prop)

-- Commutativity

example : p ∧ q ↔ q ∧ p :=
  ⟨fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩⟩

example : p ∨ q ↔ q ∨ p :=
  ⟨fun h => Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq),
  fun h => Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)⟩

-- Associativity

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨fun h => ⟨h.left.left, h.left.right, h.right⟩, fun h => ⟨⟨h.left, h.right.left⟩,h.right.right⟩⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨fun h => Or.elim h
    (fun h₁ : p ∨ q => Or.elim h₁ (fun h₃ => Or.inl h₃) (fun h₄ => Or.inr (Or.intro_left r h₄)))
    (fun h₂ : r => Or.intro_right p (Or.intro_right q h₂))
  ,fun h => Or.elim h
    (fun h₅ : p => Or.inl (Or.intro_left q h₅))
    (fun h₆ : (q ∨ r) => Or.elim h₆ (fun h₇ => Or.inl (Or.intro_right p h₇)) (fun h₈ => Or.inr h₈))⟩

-- Distributivity

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨fun h => have hp : p := h.left;
  Or.elim h.right (fun hq => Or.inl ⟨hp, hq⟩) (fun hr =>  Or.inr ⟨hp, hr⟩),
  fun h => Or.elim h (fun h₁ : p ∧ q => ⟨ h₁.left, Or.intro_left r h₁.right⟩)
  (fun h₂ : p ∧ r => ⟨ h₂.left, Or.intro_right q h₂.right⟩)⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨fun h => Or.elim h (fun hp => ⟨Or.intro_left q hp, Or.intro_left r hp⟩)
  (fun h₁ : q ∧ r => ⟨ Or.intro_right p h₁.left, Or.intro_right p h₁.right ⟩),
  fun h => Or.elim h.left (fun hp => Or.inl hp)
  (fun hq => Or.elim h.right (fun hp => Or.inl hp) (fun hr => Or.inr ⟨hq, hr⟩))⟩

-- Other properties

example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨fun h => fun pq : p ∧ q => h (pq.left) (pq.right),
  fun h => fun (hp : p) (hq : q) => h ⟨hp, hq⟩⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨fun h => ⟨fun hp : p => h (Or.intro_left q hp), fun hq : q => h (Or.inr hq)⟩ ,
  fun h => fun h₁ : p ∨ q => Or.elim h₁ (fun hp => h.left hp) (fun hq => h.right hq)⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨fun h => ⟨fun hp : p => h (Or.inl hp), fun hq : q => h (Or.inr hq)⟩,
  fun h => have np := h.left; have nq := h.right; fun porq => Or.elim porq (fun hp => np hp) (fun hq => nq hq)⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun h => Or.elim h (fun np => fun h₁ => np h₁.left) (fun nq => fun h₂ => nq h₂.right)

example : ¬(p ∧ ¬p) :=
  fun h : p ∧ ¬ p => h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  fun h => fun pimpq => h.right (pimpq h.left)

example : ¬p → (p → q) :=
  fun np => fun p => absurd p np

example : (¬p ∨ q) → (p → q) :=
  fun h => fun hp => Or.elim h (fun np => absurd hp np) (fun q => q)

example : p ∨ False ↔ p :=
  ⟨fun h => Or.elim h (fun hp => hp) (fun l => False.elim l), fun hp => Or.inl hp⟩

example : p ∧ False ↔ False :=
  ⟨fun h => h.right, False.elim⟩

example : (p → q) → (¬q → ¬p) :=
  fun h => fun nq => fun hp => nq (h hp)


open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h => Or.elim (em p)
    (fun hp => have qorr := h hp; Or.elim qorr (fun hq => Or.inl (fun _ => hq)) (fun hr => Or.inr (fun _ => hr)))
    (fun np => Or.inl (fun hp: p => absurd hp np))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  fun h => Or.elim (em p)
    (fun hp => Or.inr (Or.elim (em q) (fun hq => absurd (And.intro hp hq) h) (fun nq => nq)))
    (fun np => Or.inl np)

example : ¬(p → q) → p ∧ ¬q :=
  fun h => Or.elim (em p) (fun hp => Or.elim (em q) (fun hq => absurd (fun _:p => hq) h) (fun nq => ⟨hp, nq⟩)) (fun np => False.elim (h (fun hp => absurd hp np)))

example : (p → q) → (¬p ∨ q) :=
  fun h => Or.elim (em p) (fun hp => Or.inr (h hp)) (fun np => Or.inl np)

example : (¬q → ¬p) → (p → q) :=
  fun h => Or.elim (em q) (fun hq => fun _ => hq) (fun nq => fun hp => absurd hp (h nq))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  fun h => Or.elim (em p) (fun hp => hp) (fun np => Or.elim (em q) (fun hq => h (fun _ => hq)) (fun _ => h (fun x => absurd x np)))

-- Hard examples (no classical logic allowed)

example : ¬(p ↔ ¬p) :=
  fun h => have mp := h.mp; have mpr := h.mpr; have np := fun hp => (mp hp) hp; have hp := mpr np; (mp hp) hp
