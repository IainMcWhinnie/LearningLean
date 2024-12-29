
def m : Nat × Nat := (3,4)

def b : Bool := true

def r : True := trivial

#check Nat → Type
#check Bool → Nat
#check Fin 1
#check List

#check b

#check m
#check hello
#check (0,1)
#eval m.fst

#check true

-- def f : Nat → Nat := λ x => x+1
-- #eval f 4
#check List.cons
#check @List.cons


def p : Prop := True
def d : p := trivial
def w : p := trivial



section someproofs
variable (a b c d e : Nat)

variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = d + 1)

-- theorem T (c : Nat) (h1: a = b) (h2 : b = c + 1) :  a = b :=
--   calc
--     a = b := h1
--     b = c + 1 := h2

--   calc f = g := h5
-- example (f g h : Nat) (h5 : f = g) (h6 : g = h + 1) : f = h + 1 :=
--       _ = h + 1 := h6
end someproofs


section testingvars

variable (α β γ : Type)
variable (g: β → γ) (f : α → β)
variable (x : α)

def compose := g (f x)

#check compose

end testingvars

#check @List
#check List

#check List.cons
#check @List.cons


universe u v

def f (α : Type u) (β : α → Type v) (a : α) (b: β a) : (a : α) × β a :=
  ⟨a, b⟩

def g (α : Type u) (β : α → Type v) (a: α) (b: β a) : Σ a : α, β a :=
  Sigma.mk a b


def as : List Nat := @List.nil Nat
#check List.nil

section bebop

variable {p : Prop}
variable {q : Prop}

theorem t1 : p → q → p := fun (hp : p) (_ : q) => hp

#print t1

theorem t1': p → q → p :=
  fun hp : p =>
  fun _ : q =>
  show p from hp

theorem t1'' (hp : p) (_ : q) : p := hp

axiom hp : p

theorem t2 : q → p := t1 hp

variable (r s : Prop)

#check @t1 (r → s) (s → r)


theorem t2' (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

theorem t3 : p → q → p ∧ q :=
  fun h₁ : p =>
  fun h₂ : q =>
  show p ∧ q from And.intro h₁ h₂

example (hp : p) (hq : q) : p ∧ q := And.intro hp hq
example (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩


#check And.intro
#check And.left

-- And.right h is the same as h.right

example (h : p ∧ q) : q ∧ p := ⟨h.right, h.left⟩

#check Or.intro_left

example (hp : p) : p ∨ q := Or.intro_left q hp

#check Or.elim

example (h : p ∨ q) : q ∨ p :=
  Or.elim h
    (fun hp : p => Or.intro_right q hp)
    (fun hq : q => Or.intro_left p hq)

example (hpq: p → q) (hnq : ¬ q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)

#check False.elim

example (hp : p) (hnp : ¬ p) : q := False.elim (hnp hp)
example (hp : p) (hnp : ¬ p) : q := absurd hp hnp

example (hnp : ¬ p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp

theorem and_swap : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h: p ∧ q => ⟨h.right, h.left⟩)
    (fun h: q ∧ p => ⟨h.right, h.left⟩)



example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  have hq : q := h.right
  show q ∧ p from ⟨ hq, hp ⟩

example (h : p ∧ q): q ∧ p :=
  have hp : p := h.left
  suffices hq : q from ⟨hq, hp⟩
  show q from h.right

open Classical

#check em p

theorem dne (h : ¬ ¬ p) : p :=
  Or.elim (em p)
    (fun hp: p => hp)
    (fun hnp : ¬ p => absurd hnp h)

-- example {p : Prop}: p ∨ ¬ p :=

example (h : ¬¬ p) : p :=
  byCases
    (fun h1 => h1)
    (fun h1 => absurd h1 h)

example (h : ¬¬ p) : p :=
  byContradiction
    (fun h1 : ¬ p => show False from h h1)


example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr (show ¬ q from fun hq : q => h ⟨hp, hq⟩ ))
    (fun hnp : ¬ p => Or.inl hnp)




end bebop
