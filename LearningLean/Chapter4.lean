example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

section Relation

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c d : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab hbc


variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ x y, r x y → r y x)

example (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r a c d (trans_r a b c hab (symm_r c b hcb)) hcd

end Relation

section Equality

#check Eq.refl
#check Eq.symm
#check Eq.trans


variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

example : a = d := (hab.trans hcb.symm).trans hcd


variable (β : Type)

example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
example : 2 + 3 = 5 := Eq.refl _

example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl

example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b := Eq.subst h1 h2
example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b := h1 ▸ h2

variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

-- #check Eq.subst h₁

example : f a = f b := congrArg f h₁
example : f a = g a := congrFun h₂ a
example : f a = g b := congr h₂ h₁

end Equality

section Numbers

variable (a b c : Nat)

example : a + 0 = a := Nat.add_zero a
example : a * 1 = a := Nat.mul_one a
example : a + b + c = a + (b + c) := Nat.add_assoc a b c
-- etc...

example (x y : Nat) : (x + y) * (x + y) = x*x + y*x + x*y + y*y :=
  have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y := Nat.mul_add (x + y) x y;
  have h2 : (x+y)*x = x*x + y*x := Nat.add_mul x y x;
  have h3 : (x+y)*y = x*y + y*y := Nat.add_mul x y y;
  have h4 : (x+y)*(x+y) = x*x + y*x + (x*y + y*y) := h3 ▸ (h2 ▸ h1);
  have h5 := h4.trans (Nat.add_assoc (x*x + y*x) (x*y) (y*y)).symm;
  h5

end Numbers

section Calcs

variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

example : a = e :=
  calc
    a = b      := h1
    _ = c + 1  := h2
    _ = d + 1  := congrArg Nat.succ h3
    _ = 1 + d  := Nat.add_comm d 1
    _ = e      := Eq.symm h4


def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁;
  let ⟨k₂, d₂⟩ := h₂;
  ⟨ k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k,rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y   := h₁
    _ =  z   := h₂
    divides _ (2*z) := divides_mul z 2

infix:50 " d " => divides

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    x d y   := h₁
    _ = z   := h₂
    _ d 2*z := divides_mul ..

end Calcs

section Exist

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hzy : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hzy)

#check @Exists.intro.{1}

section
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 (hg : g 0 0 = 0): ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0) : ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0) : ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0) : ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4
end

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
  (fun w =>
  fun hw : p w ∧ q w => ⟨ w, ⟨hw.right, hw.left⟩⟩)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

-- example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
--   fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (a b : Nat) (h₁ : is_even a) (h₂ : is_even b) : is_even (a+b) :=
  Exists.elim h₁ (fun k₁ => fun d₁ =>
  Exists.elim h₂ (fun k₂ => fun d₂ =>
  Exists.intro (k₁ + k₂) (by rw [d₁, d₂, ←Nat.mul_add 2 k₁ k₂])))

theorem even_plus_even' (a b : Nat) (h₁ : is_even a) (h₂ : is_even b) : is_even (a+b) :=
  match h₁, h₂ with
  | ⟨w₁, hw₁⟩, ⟨w₂, hw₂⟩ => ⟨w₁ + w₂, by rw [hw₁, hw₂, Nat.mul_add]⟩

open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        (fun x => (fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩;
        show False from h1 h4))
      show False from h h2)

end Exist
