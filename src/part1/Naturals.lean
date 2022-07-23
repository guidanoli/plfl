namespace Naturals

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

open Nat

def convert : _root_.Nat → Nat
  | _root_.Nat.zero    =>  zero
  | _root_.Nat.succ n  =>  succ (convert n)

instance (n : _root_.Nat) : OfNat Nat n where
  ofNat := convert n

def add : Nat → Nat → Nat
  | m , zero   => m
  | m , succ n => succ (add m n)

-- from lean4/src/Init/Prelude.lean
-- class Add (α : Type) where
--   add : α → α → α 
-- class Mul (α : Type) where
--   mul : α → α → α 

-- from lean4/src/Init/Notation.lean (simplified)
-- infixl:65 " + "   => Add.add
-- infixl:70 " * "   => Mul.mul

instance : Add Nat where
  add := add

example : 3 + 2 = (5 : Nat) :=
  calc
    3 + 2
      =  succ (3 + 1)         := rfl
    _ =  succ (succ (3 + 0))  := rfl
    _ =  succ (succ 3)        := rfl
    _ =  (5 : Nat)            := rfl

-- a shorter proof
example : 3 + 2 = 5 := rfl

def mul : Nat → Nat → Nat
  | _ , zero   => zero
  | m , succ n => (mul m n) + m

instance : Mul Nat where
  mul := mul

example : 3 * 2 = (6 : Nat) :=
  calc
    3 * 2
      =  (3 * 1 + 3 : Nat)     := rfl
    _ =  (3 * 0 + 3 + 3 : Nat) := rfl
    _ =  (0 + 3 + 3 : Nat)     := rfl
    _ =  (6 : Nat)             := rfl

def monus : Nat → Nat → Nat
  | m      , zero    =>  m
  | zero   , succ _  =>  zero
  | succ m , succ n  =>  monus m n

instance : Sub Nat where
  sub := monus

example : 3 - 2 = (1 : Nat) :=
  calc
    3 - 2
      =  (2 - 1 : Nat)  := rfl
    _ =  (1 - 0 : Nat)  := rfl
    _ =  (1 : Nat)      := rfl

example : 2 - 3 = (0 : Nat) :=
  calc
    2 - 3
      =  (1 - 2 : Nat)  := rfl
    _ =  (0 - 1 : Nat)  := rfl
    _ =  (0 : Nat)      := rfl

def monus1 : Nat → Nat
| zero => zero
| succ n => n

theorem invert (m n : Nat) : succ m = succ n → m = n
  := by
    intro succ_m_eq_succ_n
    calc
      m = monus1 (succ m)  := by rfl
      _ = monus1 (succ n)  := by rw [succ_m_eq_succ_n]
      _ = n                := by rfl

def is_zero : Nat → Prop
| zero => True
| succ _ => False

theorem invert' (m n : Nat) (h : succ m = succ n) : m = n
  := by injection h with h' ; exact h'  

theorem succ_neq_zero (n : Nat) (h : succ n = zero) : False
  := by injection h

theorem succ_neq_zero' (n : Nat) (h : succ n = zero) : False
  := by contradiction
  
-- Exercises

-- seven
example : (7 : Nat) = succ (succ (succ (succ (succ (succ (succ zero)))))) := rfl

-- +-example
example : 3 + 4 = (7 : Nat) :=
  calc
    3 + 4
      = (succ (3 + 3) : Nat)                      := rfl
    _ = (succ (succ (3 + 2)) : Nat)               := rfl
    _ = (succ (succ (succ (3 + 1))) : Nat)        := rfl
    _ = (succ (succ (succ (succ (3 + 0)))) : Nat) := rfl
    _ = (succ (succ (succ (succ 3))) : Nat)       := rfl
    _ = (7 : Nat)                                 := rfl

-- *-example
example : 3 * 4 = (12 : Nat) :=
  calc
    3 * 4
      = ((3 * 3) + 3 : Nat) := rfl
    _ = (((3 * 2) + 3) + 3 : Nat) := rfl
    _ = ((((3 * 1) + 3) + 3) + 3 : Nat) := rfl
    _ = (((((3 * 0) + 3) + 3) + 3) + 3 : Nat) := rfl
    _ = ((((0 + 3) + 3) + 3) + 3 : Nat) := rfl
    _ = (12 : Nat) := rfl

-- _^_
def pow : Nat -> Nat -> Nat
| _, zero => 1
| m, succ n => m * (pow m n)

-- from lean4/src/Init/Notation.lean (simplified)
-- infixr:80 " ^ "   => Pow.Pow
instance : Pow Nat Nat where
  pow := pow

example : 3 ^ 4 = (81 : Nat) :=
  calc
    3 ^ 4
      = (3 * (3 ^ 3) : Nat) := rfl
    _ = (3 * (3 * (3 ^ 2)) : Nat) := rfl
    _ = (3 * (3 * (3 * (3 ^ 1))) : Nat) := rfl
    _ = (3 * (3 * (3 * (3 * (3 ^ 0)))) : Nat) := rfl
    _ = (3 * (3 * (3 * (3 * 1))) : Nat) := rfl
    _ = (81 : Nat) := rfl

-- 0∸n≡0 (No, it did not require induction...)
theorem zero_monus : ∀ (n : Nat), zero - n = zero
| zero => rfl
| succ _ => rfl

theorem monus_zero : ∀ (n : Nat), n - zero = n
| zero => rfl
| succ _ => rfl