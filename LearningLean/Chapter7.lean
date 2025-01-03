
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
