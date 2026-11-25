/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Data.Nat

noncomputable section

@[expose] public section

namespace Omega

/-- A nonnegative integer or the negative of a natural successor. -/
inductive Int where
  | ofNat (n : Nat)
  | negSucc (n : Nat)

namespace Int

/-- Negation of a natural number, retaining zero as a nonnegative integer. -/
def negOfNat (n : Nat) : Int :=
  Nat.rec (ofNat Nat.zero) (fun k _ => negSucc k) n

/-- Non-truncating subtraction, by deleting a successor from both operands. -/
def subNatNat (m n : Nat) : Int :=
  Nat.rec (motive := fun _ => Nat → Int) negOfNat
    (fun a diff b => Nat.rec (ofNat (Nat.succ a)) (fun k _ => diff k) b) m n

protected def neg (a : Int) : Int :=
  Int.rec negOfNat (fun n => ofNat (Nat.succ n)) a

protected def add (a b : Int) : Int :=
  Int.rec
    (fun m => Int.rec (fun n => ofNat (Nat.add m n)) (fun n => subNatNat m (Nat.succ n)) b)
    (fun m => Int.rec (fun n => subNatNat n (Nat.succ m)) (fun n => negSucc (Nat.succ (Nat.add m n))) b)
    a

protected def sub (a b : Int) : Int := a.add b.neg

protected def mul (a b : Int) : Int :=
  Int.rec
    (fun m => Int.rec (fun n => ofNat (Nat.mul m n)) (fun n => negOfNat (Nat.mul m (Nat.succ n))) b)
    (fun m => Int.rec (fun n => negOfNat (Nat.mul (Nat.succ m) n))
      (fun n => ofNat (Nat.mul (Nat.succ m) (Nat.succ n))) b)
    a

def natAbs (a : Int) : Nat := Int.rec (fun n => n) Nat.succ a

def NonNeg (a : Int) : Prop :=
  Int.rec (motive := fun _ => Prop) (fun _ => True) (fun _ => False) a

theorem NonNeg.mk (n : Nat) : NonNeg (ofNat n) := True.intro

protected def le (a b : Int) : Prop := NonNeg (b.sub a)

protected def lt (a b : Int) : Prop := (a.add (ofNat (Nat.succ Nat.zero))).le b

end Int
end Omega
