-- Exercises from Chapter 4: Quantifiers and Equalitys

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

set_option linter.unusedVariables false

-- Exercise 1

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨fun h => ⟨fun a => (h a).left, fun a => (h a).right⟩,
  fun h => fun a => ⟨h.left a, h.right a⟩⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h1 h2 a => h1 a (h2 a)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h a => Or.elim h
    (fun hl => Or.inl (hl a))
    (fun hr => Or.inr (hr a))

-- Exercise 2

example : α → ((∀ x : α, r) ↔ r) :=
  fun a => ⟨fun im => im a, fun hr => fun _ => hr⟩

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  ⟨fun h => Or.elim (em r) (fun hr => Or.inr hr) (fun nhr => Or.inl (fun x =>
  Or.elim (h x) (id) (fun hr => absurd hr nhr))),
  fun h => fun x => Or.elim h (fun hl => Or.inl (hl x)) (fun hr => Or.inr hr)⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  ⟨fun h hr x => (h x) hr,
  fun h x hr => (h hr) x⟩

-- Exercise 3
section BarberShop

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have doesHeShaveHimself := h barber;
  have cannotShaveHimself := fun x => (doesHeShaveHimself.mp x) x;
  have heShavesHimself := doesHeShaveHimself.mpr cannotShaveHimself;
  cannotShaveHimself heShavesHimself

end BarberShop

-- Exercise 4

def even (n : Nat) : Prop := ∃ k, n = 2*k

def divides (p q : Nat) : Prop := ∃ k, q = p*k

def prime (n : Nat) : Prop := n ≠ 1 ∧ (∀ p, divides p n → (p = 1 ∨ p = n))

def infinitely_many_primes : Prop := ∀ p, prime p → ∃ p', p' > p ∧ prime p'

def Fermat_prime (n : Nat) : Prop := prime n ∧ (∃ k, n = 2^(2^k))

def infinitely_many_Fermat_primes : Prop := ∀ p, Fermat_prime p → ∃ p', p' > p ∧ Fermat_prime p'

def goldbach_conjecture : Prop := ∀ n, even n → ∃ p q, n = p + q ∧ prime p ∧ prime q

def Goldbach's_weak_conjecture : Prop := ∀ n, (n > 5) ∧ (¬ even n) → ∃ p q r, (prime p ∧ prime q ∧ prime r) ∧ n = p + q + r

def Fermat's_last_theorem : Prop := ∀ n ≥ 3, ¬ ∃ a b c, (a > 0) ∧ (b > 0) ∧ (c > 0) ∧ ( a^n + b^n = c^n )

-- Exercise 5

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

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  ⟨fun h =>
  byContradiction fun nh =>
  suffices w : (∀ (x : α), p x) from h w
  fun x => Or.elim (em (p x)) (fun h₁ => h₁) (fun h₂ =>
  have w₁ : (∃ x, ¬p x) := ⟨x, h₂⟩
  absurd w₁ nh),
  fun h => match h with
  | ⟨x , hx⟩ => fun h₂ => hx (h₂ x)⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  ⟨fun h1 => fun h2 => match h2 with
  | ⟨x, hx⟩ =>
  have w := h1 x; w hx,
  fun h1 => fun x => fun px => h1 (⟨x, px⟩)⟩

-- https://en.wikipedia.org/wiki/Drinker_paradox

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  ⟨fun ⟨x, h1⟩ => fun h2 => h1 (h2 x),
  fun h => Or.elim (em (∀ x, p x)) (fun h1 => ⟨a, fun _ => h h1⟩)
  (fun h2 =>
  have w : (∃ (x:α), ¬ p x):= (byContradiction fun nh =>
  suffices w2 : (∀ (x:α), p x) from h2 w2
  fun x => Or.elim (em (p x)) (id) (fun npx => absurd ⟨x, npx⟩ nh));
  match w with
  | ⟨x, hx⟩ => ⟨x, fun nhx => absurd nhx hx⟩)
  ⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  ⟨fun h => fun hr => match h with
  | ⟨x, hx⟩ => ⟨x, hx hr⟩,
  fun h => Or.elim (em r) (fun hr => match h hr with
  | ⟨x, hx⟩ => ⟨x, fun _ => hx⟩) (fun nhr => ⟨a, fun hr => absurd hr nhr⟩)⟩
