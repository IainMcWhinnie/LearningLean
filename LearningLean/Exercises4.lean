-- Exercises from Chapter 7

-- Exercise 1

namespace Hidden

open Nat

def mul (m n : Nat) : Nat :=
  match m with
  | Nat.zero => 0
  | succ k => n + mul k n

def pred (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | succ k => k

def truncSub (m n : Nat) : Nat :=
  match n with
  | 0 => m
  | succ k => pred (truncSub m k)

def exp (m n : Nat) : Nat :=
  match n with
  | 0 => 1
  | succ k => mul m (exp m k)


theorem zero_mul (m : Nat) : mul 0 m = 0 := rfl

theorem mul_zero (n : Nat) : mul n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc mul (k+1) 0
      _ = 0 + mul k 0 := rfl
      _ = mul k 0 := by rw[Nat.zero_add]
      _ = 0 := by rw[ih]

theorem succ_mul (m n : Nat) : mul (succ m) n = n + mul m n := rfl

theorem mul_succ (m n : Nat) : mul m (succ n) = m + mul m n := by
  induction m with
  | zero => rw [Nat.zero_add, zero_mul, zero_mul];
  | succ k ih => rw [succ_mul, succ_mul, Nat.add_comm k 1, Nat.add_assoc 1 k, ← Nat.add_assoc k n, Nat.add_comm k n, Nat.add_assoc n k, ←ih, ← Nat.add_assoc, Nat.add_comm 1 n];

theorem mul_comm (m n : Nat) : mul m n = mul n m := by
  induction n with
  | zero => rw [mul_zero, zero_mul]
  | succ k ih => rw [mul_succ, succ_mul,ih]

theorem mul_add (l m n : Nat) : mul l (m + n) = mul l m + mul l n := by
  induction l with
  | zero => repeat rw [zero_mul]
  | succ k ih => rw [succ_mul, succ_mul, succ_mul]; rw [ih]; rw [Nat.add_assoc m n, ←Nat.add_assoc n (mul k m), Nat.add_comm n (mul k m), Nat.add_assoc (mul k m) n, ←Nat.add_assoc m]

theorem mul_assoc (l m n : Nat) : mul (mul l m) n = mul l (mul m n) := by
  induction n with
  | zero => rw [mul_zero, mul_zero, mul_zero]
  | succ k ih => rw [mul_succ, mul_succ, mul_add, ih]

theorem add_mul (l m n : Nat) : mul (l + m) n = mul l n + mul m n := by
  rw [mul_comm, mul_add, mul_comm, mul_comm n]

theorem mul_one (n : Nat) : mul n 1 = n := by
  rw [mul_succ, mul_zero, Nat.add_zero]

theorem one_mul (n : Nat) : mul 1 n = n := by
  rw [mul_comm, mul_one]

theorem succ_pred (n : Nat) (h : n ≠ 0): succ (pred n) = n := by
  induction n
  contradiction
  rfl

theorem pred_succ (n : Nat) : pred (succ n) = n := by rfl

theorem pred_is_truncSub_one (n : Nat) : pred n = truncSub n 1 := by rfl

theorem exp_succ (n a : Nat) : exp n (succ a) = mul n (exp n a) := rfl

theorem exp_zero (n : Nat) : exp n 0 = 1 := rfl

theorem exp_add (n a b : Nat) : exp n (a + b) = mul (exp n a) (exp n b) := by
  induction b with
  | zero => rw [Nat.add_zero, exp_zero, mul_one]
  | succ k ih => rw[←Nat.add_assoc a k 1, exp_succ, ih, exp_succ, ←mul_assoc n (exp n a), mul_comm n (exp n a), mul_assoc]

theorem exp_exp (n a b : Nat) : exp (exp n a) b = exp n (mul a b) := by
  induction b with
  | zero => rw [exp_zero, mul_zero, exp_zero]
  | succ k ih => rw [exp_succ, ih, mul_succ, exp_add]

theorem succ_neq_zero (n : Nat) : succ n ≠ 0 := by
  intro h
  injection h



-- Exercise 2

open List

def length {α : Type} (as : List α) : Nat :=
  match as with
  | nil => 0
  | _ :: tail => 1 + length tail

theorem nil_append (as : List α) : nil ++ as = as := by rfl

theorem length_nil {α : Type} : length (α := α) nil = 0 := rfl

theorem length_append (α : Type) (s t : List α) : length (s ++ t) = length s + length t := by
  induction s with
  | nil => rw [length_nil, Nat.zero_add, nil_append]
  | cons a as ih => calc length (a :: as ++ t)
    _ = 1 + length (as ++ t) := rfl
    _ = 1 + length as + length t := by rw [ih, Nat.add_assoc]
    _ = length (a :: as) + length t := by rfl


theorem append_nil (as : List α) : as ++ nil = as := by
  induction as with
  | nil => rw [nil_append]
  | cons a s ih => calc a::s ++ []
    _ = a :: (s ++ []) := by rfl
    _ = a :: s := by rw [ih]

#print List.append

-- def append (as bs : List α) : List α :=
--   match as with
--   | nil       => bs
--   | cons a as => cons a (append as bs)

theorem append_assoc (as bs cs : List α) : (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction as with
  | nil => rw [nil_append, nil_append]
  | cons a s ih => calc a::s ++ bs ++ cs
    _ = a :: (s++bs) ++ cs := by rfl
    _ = a :: (s++bs++cs) := by rfl
    _ = a :: (s++(bs++cs)) := by rw [ih]
    _ = a::s ++ (bs++cs) := by rfl

def reverse {α : Type} (as : List α) : List α :=
  match as with
  | [] => []
  | a::s => (reverse s) ++ [a]

#eval reverse [1,2,3]

theorem length_reverse {α : Type} (t : List α) : length (reverse t) = length t := by
  induction t with
  | nil => rfl
  | cons a s ih => calc length (reverse (a::s))
    _ = length ((reverse s) ++ [a]) := by rfl
    _ = length (reverse s) + length [a] := by rw [length_append]
    _ = length [a] + length (reverse s) := by rw [Nat.add_comm]
    _ = length [a] + length s := by rw [ih]
    _ = length ([a] ++ s) := by rw [← length_append]
    _ = length (a :: s) := by rfl


theorem reverse_append {α : Type} (s t : List α) : reverse (s ++ t) = reverse t ++ reverse s := by
  induction s with
  | nil => rw [nil_append, reverse.eq_1, append_nil]
  | cons h tail ih =>
  calc reverse (h :: tail ++ t)
    _ = reverse (h :: (tail ++ t)) := by rfl
    _ = reverse (tail ++ t) ++ [h] := by rfl
    _ = reverse t ++ reverse tail ++ [h] := by rw [ih]
    _ = reverse t ++ (reverse tail ++ [h]) := by rw [append_assoc]
    _ = reverse t ++ reverse (h::tail) := by rfl

theorem reverse_idem {α : Type} (t : List α) : reverse (reverse t) = t := by
  induction t with
  | nil => rfl
  | cons a s ih =>
  calc reverse (reverse (a::s) )
    _ = reverse (reverse s ++ [a]) := by rfl
    _ = reverse [a] ++ reverse (reverse s) := by rw [reverse_append]
    _ = [a] ++ reverse (reverse s) := by rfl
    _ = [a] ++ s                   := by rw [ih]
    _ = a :: s                     := by rfl

end Hidden
