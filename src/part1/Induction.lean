open Nat

namespace Induction

example : 3 + (4 + 5) = (3 + 4) + 5 :=
  calc
    3 + (4 + 5)
      =  3 + 9        := rfl
    _ =  12           := rfl
    _ =  7 + 5        := rfl
    _ =  (3 + 4) + 5  := rfl

theorem add_zero (m : Nat)   : m + zero     = m            := rfl
theorem add_succ (m n : Nat) : m + (succ n) = succ (m + n) := rfl

theorem add_assoc : ∀ (m n p : Nat), m + (n + p) = (m + n) + p
  | m , n , zero =>
    calc
      m + (n + zero)
        = m + n               := by rw [add_zero n]
      _ = (m + n) + zero      := by rw [add_zero (m + n)]
  | m , n , succ p =>
    calc
      m + (n + succ p)
        = m + succ (n + p)    := by rw [add_succ n p]
      _ = succ (m + (n + p))  := by rw [add_succ m (n + p)]
      _ = succ ((m + n) + p)  := by rw [add_assoc m n p]
      _ = (m + n) + succ p    := by rw [add_succ (m + n) p]

theorem add_assoc' : ∀ (m n p : Nat), m + (n + p) = (m + n) + p
  := by
      intros m n p
      induction p with
      | zero =>
          calc
            m + (n + zero)
              = m + n               := by rfl
            _ = (m + n) + zero      := by rfl
      | succ p ih =>
          calc
            m + (n + succ p)
              = m + succ (n + p)    := by rfl
            _ = succ (m + (n + p))  := by rfl
            _ = succ ((m + n) + p)  := by rw [ih]
            _ = (m + n) + succ p    := by rfl


theorem zero_add : ∀ (n : Nat), zero + n = n
  | zero =>
    calc
      zero + zero
        = zero              := rfl
  | succ n => 
    calc
      zero + succ n
        =  succ (zero + n)  := rfl
      _ =  succ n           := by rw [zero_add n]

theorem succ_add : ∀ (m n : Nat), (succ m) + n = succ (m + n)
  | m , zero =>
    calc
      (succ m) + zero
        = succ m            := rfl
      _ = succ (m + zero)   := rfl
  | m , succ n =>
    calc
      (succ m) + (succ n)
        = succ ((succ m) + n)  := rfl
      _ = succ (succ (m + n))  := by rw [succ_add m n]
      _ = succ (m + (succ n))  := rfl

theorem comm_add : ∀ (m n : Nat), m + n = n + m
  | zero , n =>
    calc
      zero + n
        = n                     := by rw [zero_add n]
      _ = n + zero              := rfl
  | succ m , n =>
    calc
      (succ m) + n
        = succ (m + n)          := by rw [succ_add m n]
      _ = succ (n + m)          := by rw [comm_add m n]
      _ = n + (succ m)          := rfl
      
  
class Zero (α : Type) where
  zero : α

instance : Zero Nat where
  zero := Nat.zero

instance [Zero α] : OfNat α 0 where
  ofNat := Zero.zero

class Monoid (α : Type) extends Add α, Zero α where
  add_assoc : ∀ (m n p : Nat), (m + n) + p = m + (n + p)
  add_zero : ∀ (n : Nat), n + 0 = n
  zero_add : ∀ (n : Nat), 0 + n = n

instance : Monoid Nat where
  add_assoc := Nat.add_assoc
  add_zero := Nat.add_zero
  zero_add := Nat.zero_add

-- exercises

-- operators

-- another pair of operators that have an identity (1) and
-- are associative (2), commutative (3) and distributive (4) are
-- the logical AND and OR.
-- 
-- (1) X AND TRUE = X
--     X OR FALSE = X
-- (2) X AND (Y AND Z) = (X AND Y) AND Z
--     X OR (Y OR Z) = (X OR Y) OR Z
-- (3) X AND (Y OR Z) = (X AND Y) OR (X AND Z)

-- A pair of operators that has an identity (1), is associative (2)
-- but is not commutative (3) is the matrix multiplication operator
--
-- A . I = A, where I is the identity matrix
-- A . (B . C) = (A . B) . C
-- There exists A and B such that A . B /= B . A

-- *-distrib-+
theorem left_distrib : ∀ (m n p : Nat),
  m * (n + p) = m * n + m * p
  :=
    by
    intros m n p
    induction p with
    | zero => rfl
    | succ p ih =>
      calc
        m * (n + succ p)
          = m * succ (n + p) := by rw [add_succ]
        _ = m * (n + p) + m := rfl
        _ = m * n + m * p + m := by rw [ih]
        _ = m * n + (m * p + m) := by rw [add_assoc]
        _ = m * n + (m * (succ p)) := rfl

-- *-assoc
theorem mul_assoc : ∀ (m n p : Nat),
  m * (n * p) = (m * n) * p
  :=
    by
    intros m n p
    induction p with
    | zero => rfl
    | succ p ih =>
      calc
        m * (n * succ p)
          = m * (n * p + n) := rfl
        _ = m * (n * p) + m * n := by rw [left_distrib]
        _ = (m * n) * p + m * n := by rw [ih]
        _ = (m * n) * succ p := rfl

theorem zero_mul : ∀ (m : Nat), zero * m = zero :=
  by
  intros m
  induction m with
  | zero => rfl
  | succ m ih =>
    calc
      zero * (succ m)
        = zero * m + zero := rfl
      _ = zero + zero     := by rw [ih]
      _ = zero            := rfl

theorem mul_one : ∀ (m : Nat), m * 1 = m :=
  by
    intros m
    calc
      m * 1
        = m * 0 + m := rfl
      _ = 0 + m     := rfl
      _ = m + 0     := by rw [comm_add]
      _ = m         := rfl

theorem one_mul : ∀ (m : Nat), 1 * m = m :=
  by
    intros m
    induction m with
    | zero => rfl
    | succ m ih =>
      calc
        1 * (succ m)
          = 1 * m + 1 := rfl
        _ = m + 1 := by rw [ih]
        _ = succ m := rfl

theorem right_distrib : ∀ (m n p : Nat),
  (m + n) * p = m * p + n * p
  :=
    by
    intros m n p
    induction p with
    | zero => rfl
    | succ p ih =>
      calc
        (m + n) * succ p
          = (m + n) * p + (m + n) := by rfl
        _ = (m * p + n * p) + (m + n) := by rw [ih]
        _ = ((m * p + n * p) + m) + n := by rw [add_assoc]
        _ = (m * p + (n * p + m)) + n := by rw [add_assoc]
        _ = (m * p + (m + n * p)) + n := by rw [comm_add m _]
        _ = ((m * p + m) + n * p) + n := by rw [add_assoc]
        _ = (m * p + m) + (n * p + n) := by rw [add_assoc]
        _ = (m * p + m) + (n * p + n) := by rw [add_assoc]
        _ = m * succ p + (n * p + n) := rfl
        _ = m * succ p + n * succ p := rfl

-- *-comm
theorem mul_comm : ∀ (m n : Nat),
  m * n = n * m
  :=
    by
    intros m n
    induction n with
    | zero =>
      calc
        m * zero
          = zero := rfl
        _ = zero * m := by rw [zero_mul]
    | succ n ih =>
      calc
        m * (succ n)
          = m * n + m := rfl
        _ = n * m + m := by rw [ih]
        _ = n * m + 1 * m := by rw [one_mul]
        _ = (n + 1) * m := by rw [right_distrib]
        _ = (succ n) * m := rfl

-- 0∸n≡0
theorem zero_sub : ∀ (n : Nat), 0 - n = 0
:=
  by
  intros n
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      0 - succ n
        = pred (0 - n) := rfl
      _ = pred 0 := by rw [ih]
      _ = 0 := rfl

-- ∸-+-assoc
theorem sub_add_assoc : ∀ (m n p : Nat), m - n - p = m - (n + p)
:=
  by
  intros m n p
  induction p with
  | zero => rfl
  | succ p ih =>
    calc
      m - n - succ p
        = pred (m - n - p) := rfl
      _ = pred (m - (n + p)) := by rw [ih]
      _ = m - succ (n + p) := rfl
      _ = m - (n + succ p) := rfl

-- +*^
theorem pow_distrib_plus_on_exponent : ∀ (m n p : Nat), m ^ (n + p) = (m ^ n) * (m ^ p)
:=
  by
  intros m n p
  induction p with
  | zero =>
    calc
      m ^ (n + 0)
        = m ^ n := rfl
      _ = (m ^ n) * 1 := by rw [mul_one]
      _ = (m ^ n) * (m ^ 0) := rfl
  | succ p ih =>
    calc
      m ^ (n + succ p)
        = m ^ succ (n + p) := rfl
      _ = m ^ (n + p) * m := rfl
      _ = (m ^ n) * (m ^ p) * m := by rw [ih]
      _ = (m ^ n) * ((m ^ p) * m) := by rw [mul_assoc]
      _ = (m ^ n) * (m ^ succ p) := rfl

theorem pow_distrib_mul_on_base : ∀ (m n p : Nat), (m * n) ^ p = (m ^ p) * (n ^ p)
:=
  by
  intros m n p
  induction p with
  | zero => rfl
  | succ p ih =>
    calc
      (m * n) ^ succ p
        = (m * n) ^ p * (m * n) := rfl
      _ = (m ^ p) * (n ^ p) * (m * n) := by rw [ih]
      _ = (m ^ p) * (n ^ p) * m * n := by rw [mul_assoc]
      _ = (m ^ p) * ((n ^ p) * m) * n := by rw [mul_assoc]
      _ = (m ^ p) * (m * (n ^ p)) * n := by rw [mul_comm m _]
      _ = (m ^ p) * m * (n ^ p) * n := by rw [mul_assoc]
      _ = (m ^ succ p) * (n ^ p) * n := rfl
      _ = (m ^ succ p) * ((n ^ p) * n) := by rw [mul_assoc]
      _ = (m ^ succ p) * (n ^ succ p) := rfl

theorem pow_mul_assoc : ∀ (m n p : Nat), (m ^ n) ^ p = m ^ (n * p)
:=
  by
  intros m n p
  induction p with
  | zero => rfl
  | succ p ih =>
    calc
      (m ^ n) ^ succ p
        = (m ^ n) ^ p * m ^ n := rfl
      _ = m ^ (n * p) * m ^ n := by rw [ih]
      _ = m ^ (n * p + n) := by rw [pow_distrib_plus_on_exponent]
      _ = m ^ (n * p + n * 1) := by rw [mul_one]
      _ = m ^ (n * (p + 1)) := by rw [left_distrib]
      _ = m ^ (n * succ p) := rfl

-- Bin
inductive Bin where
  | nothing : Bin
  | _O : Bin → Bin
  | _I : Bin → Bin

notation:80 "<>" => Bin.nothing
notation:80 b " O" => Bin._O b
notation:80 b " I" => Bin._I b

example : <> O I = Bin._I (Bin._O Bin.nothing) := rfl

def inc : Bin → Bin
  | <> => <> I
  | b O => b I
  | b I => (inc b) O

example: inc (<>      ) = <>     I := rfl
example: inc (<>     O) = <>     I := rfl
example: inc (<>     I) = <>   I O := rfl
example: inc (<>   I O) = <>   I I := rfl
example: inc (<>   I I) = <> I O O := rfl
example: inc (<> I O O) = <> I O I := rfl

def to_bin : Nat → Bin
  | zero => <> O
  | succ n => inc (to_bin n)

def from_bin : Bin → Nat
  | <> => zero
  | b O => (from_bin b) + (from_bin b)
  | b I => succ ((from_bin b) + (from_bin b))

example : from_bin (to_bin 0) = 0 := rfl
example : from_bin (to_bin 1) = 1 := rfl
example : from_bin (to_bin 2) = 2 := rfl
example : from_bin (to_bin 3) = 3 := rfl
example : from_bin (to_bin 4) = 4 := rfl

-- Bin-laws
theorem from_inc_is_suc_from : ∀ (b : Bin),
  from_bin (inc b) = succ (from_bin b)
:=
  by
  intros b
  induction b with
  | nothing => rfl
  | _O b => rfl
  | _I b ih =>
    calc
      from_bin (inc (b I))
        = from_bin ((inc b) O) := rfl
      _ = from_bin (inc b) + from_bin (inc b) := rfl
      _ = succ (from_bin b) + from_bin (inc b) := by rw [ih]
      _ = succ (from_bin b) + succ (from_bin b) := by rw [ih]
      _ = succ (from_bin b) + succ (from_bin b) := rfl
      _ = succ (succ (from_bin b) + (from_bin b)) := rfl
      _ = succ ((from_bin b) + succ (from_bin b)) := by rw [comm_add]
      _ = succ (succ (from_bin b + from_bin b)) := rfl
      _ = succ (from_bin (b I)) := rfl

-- Counter-example for "to (from b) ≡ b"
example : to_bin (from_bin Bin.nothing) = Bin._O Bin.nothing := rfl

theorem from_to_bin : ∀ (n : Nat), from_bin (to_bin n) = n
:=
  by
  intros n
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      from_bin (to_bin (succ n))
        = from_bin (inc (to_bin n)) := rfl
      _ = succ (from_bin (to_bin n)) := by rw [from_inc_is_suc_from]
      _ = succ n := by rw [ih]