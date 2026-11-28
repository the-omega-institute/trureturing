/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Data.Nat.Basic
public import OmegaInit.Data.Cast

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
  Nat.casesOn n (ofNat Nat.zero) negSucc

end Int
end Omega

port_definition Int.negOfNat.match_1 with_native_code
port_definition Int.subNatNat with_native_code

namespace Omega.Int

protected def neg : Int → Int := fun a =>
  Int.casesOn a negOfNat (fun n => ofNat (Nat.succ n))

protected def add : Int → Int → Int := fun a b =>
  Int.casesOn a
    (fun m => Int.casesOn b (fun n => ofNat (Nat.add m n)) (fun n => subNatNat m (Nat.succ n)))
    (fun m => Int.casesOn b (fun n => subNatNat n (Nat.succ m)) (fun n => negSucc (Nat.succ (Nat.add m n))))

protected def sub : Int → Int → Int := fun a b => a.add b.neg

protected def mul : Int → Int → Int := fun a b =>
  Int.casesOn a
    (fun m => Int.casesOn b (fun n => ofNat (Nat.mul m n)) (fun n => negOfNat (Nat.mul m (Nat.succ n))))
    (fun m => Int.casesOn b (fun n => negOfNat (Nat.mul (Nat.succ m) n))
      (fun n => ofNat (Nat.mul (Nat.succ m) (Nat.succ n))))

def natAbs : Int → Nat := fun a => Int.casesOn a (fun n => n) Nat.succ

/-- The sign of an integer, with the zero case distinguished. -/
def sign : Int → Int := fun a =>
  Int.casesOn a (fun n => Nat.casesOn n (ofNat Nat.zero) (fun _ => ofNat Nat.zero.succ))
    (fun _ => negSucc Nat.zero)

/-- Discard a negative input and retain the magnitude of a nonnegative input. -/
def toNat : Int → Nat := fun a => Int.casesOn a (fun n => n) (fun _ => Nat.zero)

inductive NonNeg : Int → Prop where
  | mk (n : Nat) : NonNeg (ofNat n)

protected def le (a b : Int) : Prop := NonNeg (b.sub a)

protected def lt (a b : Int) : Prop := (a.add (ofNat (Nat.succ Nat.zero))).le b

end Omega.Int

port_definition instOfNat with_native_code
port_definition instNatCastInt with_native_code
port_definition Int.instNegInt
port_definition Int.instAdd
port_definition Int.instSub
port_definition Int.instMul
port_definition Int.instLEInt
port_definition Int.instLTInt
port_definition Int.instDvd
port_definition Int.neg.match_1 with_native_code
port_proof Int.decNonneg._proof_1
port_definition Int.decNonneg
port_definition Int.decLe
port_definition Int.decLt

attribute [instance] Omega.instOfNat Omega.instNatCastInt Omega.Int.instNegInt
attribute [instance] Omega.Int.instAdd Omega.Int.instSub Omega.Int.instMul
attribute [instance] Omega.Int.instLEInt Omega.Int.instLTInt Omega.Int.instDvd

attribute [instance] Omega.Int.decLe Omega.Int.decLt
