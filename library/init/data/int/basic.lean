/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

The integers, with addition, multiplication, and subtraction.
-/
prelude
import init.data.nat
import init.data.string
import init.data.repr
import init.data.to_string
import init.coe
open nat

/- the type, coercions, and notation -/

inductive int : Type
| of_nat : nat → int
| neg_succ_of_nat : nat → int

notation `ℤ` := int

instance : has_coe nat int := ⟨int.of_nat⟩

notation `-[1+ ` n `]` := int.neg_succ_of_nat n

protected def int.repr : int → string
| (int.of_nat n)          := repr n
| (int.neg_succ_of_nat n) := "-" ++ repr (succ n)

instance : has_repr int :=
⟨int.repr⟩

instance : has_to_string int :=
⟨int.repr⟩

namespace int

protected lemma coe_nat_eq (n : ℕ) : ↑n = int.of_nat n := rfl

protected def zero : ℤ := of_nat 0
protected def one  : ℤ := of_nat 1

instance : has_zero ℤ := ⟨int.zero⟩
instance : has_one ℤ := ⟨int.one⟩

lemma of_nat_zero : of_nat (0 : nat) = (0 : int) := rfl

lemma of_nat_one : of_nat (1 : nat) = (1 : int) := rfl

/- definitions of basic functions -/

def neg_of_nat : ℕ → ℤ
| 0        := 0
| (succ m) := -[1+ m]

def sub_nat_nat (m n : ℕ) : ℤ :=
match (n - m : nat) with
| 0        := of_nat (m - n)  -- m ≥ n
| (succ k) := -[1+ k]         -- m < n, and n - m = succ k
end

protected def neg : ℤ → ℤ
| (of_nat n) := neg_of_nat n
| -[1+ n]    := succ n

protected def add : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m + n)
| (of_nat m) -[1+ n]    := sub_nat_nat m (succ n)
| -[1+ m]    (of_nat n) := sub_nat_nat n (succ m)
| -[1+ m]    -[1+ n]    := -[1+ succ (m + n)]

protected def mul : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m * n)
| (of_nat m) -[1+ n]    := neg_of_nat (m * succ n)
| -[1+ m]    (of_nat n) := neg_of_nat (succ m * n)
| -[1+ m]    -[1+ n]    := of_nat (succ m * succ n)

instance : has_neg ℤ := ⟨int.neg⟩
instance : has_add ℤ := ⟨int.add⟩
instance : has_mul ℤ := ⟨int.mul⟩

-- defeq to algebra.sub which gives subtraction for arbitrary `add_group`s
protected def sub : ℤ → ℤ → ℤ :=
λ m n, m + -n

instance : has_sub ℤ := ⟨int.sub⟩

protected lemma neg_zero : -(0:ℤ) = 0 := rfl

/- neg -/

protected lemma neg_neg : ∀ a : ℤ, -(-a) = a
| (of_nat 0)     := rfl
| (of_nat (n+1)) := rfl
| -[1+ n]        := rfl

/- nat_abs -/

@[simp] def nat_abs : ℤ → ℕ
| (of_nat m) := m
| -[1+ m]    := succ m

/- sign -/

def sign : ℤ → ℤ
| (n+1:ℕ) := 1
| 0       := 0
| -[1+ n] := -1

/- Quotient and remainder -/

-- There are three main conventions for integer division,
-- referred here as the E, F, T rounding conventions.
-- All three pairs satisfy the identity x % y + (x / y) * y = x
-- unconditionally.

-- E-rounding: This pair satisfies 0 ≤ mod x y < nat_abs y for y ≠ 0
protected def div : ℤ → ℤ → ℤ
| (m : ℕ) (n : ℕ) := of_nat (m / n)
| (m : ℕ) -[1+ n] := -of_nat (m / succ n)
| -[1+ m] 0       := 0
| -[1+ m] (n+1:ℕ) := -[1+ m / succ n]
| -[1+ m] -[1+ n] := of_nat (succ (m / succ n))

protected def mod : ℤ → ℤ → ℤ
| (m : ℕ) n := (m % nat_abs n : ℕ)
| -[1+ m] n := sub_nat_nat (nat_abs n) (succ (m % nat_abs n))

-- F-rounding: This pair satisfies fdiv x y = floor (x / y)
def fdiv : ℤ → ℤ → ℤ
| 0       _       := 0
| (m : ℕ) (n : ℕ) := of_nat (m / n)
| (m+1:ℕ) -[1+ n] := -[1+ m / succ n]
| -[1+ m] 0       := 0
| -[1+ m] (n+1:ℕ) := -[1+ m / succ n]
| -[1+ m] -[1+ n] := of_nat (succ m / succ n)

def fmod : ℤ → ℤ → ℤ
| 0       _       := 0
| (m : ℕ) (n : ℕ) := of_nat (m % n)
| (m+1:ℕ) -[1+ n] := sub_nat_nat (m % succ n) n
| -[1+ m] (n : ℕ) := sub_nat_nat n (succ (m % n))
| -[1+ m] -[1+ n] := -of_nat (succ m % succ n)

-- T-rounding: This pair satisfies quot x y = round_to_zero (x / y)
def quot : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m / n)
| (of_nat m) -[1+ n]    := -of_nat (m / succ n)
| -[1+ m]    (of_nat n) := -of_nat (succ m / n)
| -[1+ m]    -[1+ n]    := of_nat (succ m / succ n)

def rem : ℤ → ℤ → ℤ
| (of_nat m) (of_nat n) := of_nat (m % n)
| (of_nat m) -[1+ n]    := of_nat (m % succ n)
| -[1+ m]    (of_nat n) := -of_nat (succ m % n)
| -[1+ m]    -[1+ n]    := -of_nat (succ m % succ n)

instance : has_div ℤ := ⟨int.div⟩
instance : has_mod ℤ := ⟨int.mod⟩

end int
