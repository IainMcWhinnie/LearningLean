open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := fun ⟨w, hr⟩ => hr

example (a : α) : r → (∃ x : α, r) := fun hr => ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  ⟨fun f =>
    match f with
    | ⟨a, ha⟩ => ⟨⟨ a, ha.left ⟩, ha.right⟩,
  fun f =>
    match f.left with
    | ⟨a, ha⟩ => ⟨a, ha, f.right⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  ⟨fun h => match h with
  | ⟨x, hx⟩ => Or.elim hx (fun hl => Or.inl ⟨x, hl⟩) (fun hr => Or.inr ⟨x, hr⟩),
  fun h => Or.elim h (fun hl => (fun ⟨z, hz⟩ => ⟨z, Or.inl hz⟩) hl)
  (fun hr => (fun ⟨y, hy⟩ => ⟨y, Or.inr hy⟩) hr)⟩


#check Exists.intro

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  ⟨fun h => fun m => match m with
  | ⟨x, hx⟩ => have c := h x; hx c,
  fun h => fun x => byContradiction fun npx => h (⟨x,npx⟩)⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  ⟨fun h => fun nh => match h with
  | ⟨x, hx⟩ => (nh x) hx,
  fun h => byContradiction fun nh =>
  suffices w : (∀ (x : α), ¬p x) from h w
  fun x => fun px => nh (⟨x, px⟩)⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  ⟨fun h => fun x => fun npx => h (⟨x, npx⟩),
  fun h => fun ex => match ex with
  | ⟨x, px⟩ => (h x) px⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
