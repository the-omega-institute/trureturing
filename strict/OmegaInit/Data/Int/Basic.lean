/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Data.Nat.Basic

noncomputable section

@[expose] public section

namespace Omega

set_option genCtorIdx false in
/-- A nonnegative integer or the negative of a natural successor. -/
inductive Int where
  | ofNat : Nat → Int
  | negSucc : Nat → Int

namespace Int

/-- Negation of a natural number, retaining zero as a nonnegative integer. -/
def negOfNat : Nat → Int := fun n =>
  Nat.rec (ofNat Nat.zero) (fun k _ => negSucc k) n

end Int
end Omega

port_definition Int.negOfNat.match_1
port_definition Int.subNatNat

namespace Omega.Int

protected def neg : Int → Int := fun a =>
  Int.rec negOfNat (fun n => ofNat (Nat.succ n)) a

protected def add : Int → Int → Int := fun a b =>
  Int.rec
    (fun m => Int.rec (fun n => ofNat (Nat.add m n)) (fun n => subNatNat m (Nat.succ n)) b)
    (fun m => Int.rec (fun n => subNatNat n (Nat.succ m)) (fun n => negSucc (Nat.succ (Nat.add m n))) b)
    a

protected def sub : Int → Int → Int := fun a b => a.add b.neg

protected def mul : Int → Int → Int := fun a b =>
  Int.rec
    (fun m => Int.rec (fun n => ofNat (Nat.mul m n)) (fun n => negOfNat (Nat.mul m (Nat.succ n))) b)
    (fun m => Int.rec (fun n => negOfNat (Nat.mul (Nat.succ m) n))
      (fun n => ofNat (Nat.mul (Nat.succ m) (Nat.succ n))) b)
    a

def natAbs : Int → Nat := fun a => Int.rec (fun n => n) Nat.succ a

/-- The sign of an integer, with the zero case distinguished. -/
def sign : Int → Int :=
  Int.rec (fun n => Nat.rec (ofNat Nat.zero) (fun _ _ => ofNat Nat.zero.succ) n)
    (fun _ => negSucc Nat.zero)

/-- Discard a negative input and retain the magnitude of a nonnegative input. -/
def toNat : Int → Nat := Int.rec (fun n => n) (fun _ => Nat.zero)

inductive NonNeg : Int → Prop where
  | mk (n : Nat) : NonNeg (ofNat n)

protected def le (a b : Int) : Prop := NonNeg (b.sub a)

protected def lt (a b : Int) : Prop := (a.add (ofNat (Nat.succ Nat.zero))).le b

end Omega.Int
