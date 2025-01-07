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


end Hidden
