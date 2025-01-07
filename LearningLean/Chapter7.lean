
inductive Foo where
  | constructor₁ : Prop → Foo

#check Foo

inductive Weekday where
  | sunday : Weekday
  | monday : Weekday
  | tuesday : Weekday
  | wednesday : Weekday
  | thursday : Weekday
  | friday : Weekday
  | saturday : Weekday
  deriving Repr

#check Weekday
#check Weekday.sunday

section

open Weekday
#check sunday

end

#check Weekday.rec

open Weekday
def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday => 7
  | monday => 1
  | tuesday => 2
  | wednesday => 3
  | thursday => 4
  | friday => 5
  | saturday => 6

#eval numberOfDay sunday

namespace Hidden

inductive Bool where
  | true : Bool
  | false : Bool

open Bool

def rand (a b : Bool) : Bool :=
  match a with
  | Bool.true => b
  | Bool.false => false

inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β
  | inr : β → Sum α β

end Hidden

def fst (α : Type u) (β : Type v) (p : Prod α β) : α :=
  match p with
  | Prod.mk a b => a

def snd (α : Type u) (β : Type v) (p : Prod α β) : β :=
  match p with
  | Prod.mk a b => b

def prod_example (p : Bool × Nat) : Nat :=
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2*n) (2*n+1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

def sum_example (s : Sum Nat Nat) : Nat :=
  Sum.casesOn (motive := fun _ => Nat) s (fun n => 2*n) (fun n => 2 * n + 1)

namespace Hidden2

structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)

end Hidden2

structure Colour where
  (red : Nat) (green : Nat) (blue : Nat)
  deriving Repr

def yellow := Colour.mk 255 255 0
#eval Colour.red yellow

structure Semigroup where
  carrier : Type
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)

def naturalNumbersSemigroup : Semigroup := Semigroup.mk Nat (fun x y => x+y) Nat.add_assoc

namespace Hidden3

inductive Sigma {α : Type} (β : α → Type v) where
  | mk : (a : α) → β a → Sigma β

inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α

end Hidden3

namespace Hidden4

-- inductive Exists {α : Type} (p : α → Prop) : Prop where
--   | intro (x : α) (h : p x) : Exists p

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

inductive Subtype {α : Type u} (p : α → Prop) where
  | mk : (x : α) → p x → Subtype p

#check @Hidden4.Exists.intro.{1}
#check @Hidden4.Subtype.mk.{0}

def isEven (x : Nat) := ∃ k, x = 2*k

#check (Subtype isEven)
#check (Exists isEven)
#check {x : Nat // isEven x}

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

-- def add (m n : Nat) :=
--   match n with
--   | zero => m
--   | (Hidden4.Nat.succ n) => succ (add m n)

end Hidden4

open Nat

example (n : Nat) : 0 + n = n :=
  Nat.recAux (motive := fun x : Nat => 0 + x = x)
  (show 0+0=0 from Nat.add_zero 0)
  (fun (m : Nat) (ih : 0 + m = m) =>
    show 0 + (succ m) = succ m from
    calc 0+(succ m)
      _ = succ (0 + m) := rfl
      _ = succ m       := by rw[ih])
  n


#check Nat.recAux

example (m n k : Nat) : m + n + k = m + (n + k) :=
  Nat.recAux (motive := fun k =>  m + n + k = m + (n + k))
  (show m + n + 0 = m + (n + 0) from rfl)
  (fun x ih => show m + n + (succ x) = m + (n + succ x) from
  calc m + n + (succ x)
    _ = succ ((m+n) + x) := rfl
    _ = succ (m + (n + x)) := by rw[ih]
    _ = m + succ (n + x) := rfl
    _ = m + (n + succ x) := rfl)
  k


example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  . exact hz
  . apply hs

example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
  cases n with
  | zero => apply absurd rfl h
  | succ m => rfl


example (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => rw [Nat.add_succ, ih]

open Nat

example (m n k : Nat) (h : succ (succ m) = succ (succ n))
        : n + k = m + k := by
  injection h with h'
  injection h' with h''
  rw [h'']

example (m n : Nat) (h : succ m = 0) : n = n + 7 := by
  injection h
