/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude

public import OmegaMath.Arithmetic.WDigits
public import OmegaMath.Data.Int

/-!
Omega original.

The parity-descending sum of the shifted Fibonacci sequence with initial values 1 and 1.
-/

noncomputable section
@[expose] public section

namespace Omega.Arithmetic.Fibonacci

/-- Fibonacci numbers indexed from the first 1. -/
def shiftedFib (k : Nat) : Int := Int.ofNat (Nat.fib k.succ)

/-- Sum of the positive indices of the same parity, up to and including `k`. -/
def alternatingSum (k : Nat) : Int :=
  (Nat.rec (motive := fun _ => Bool → Int) (Bool.rec Int.zero (shiftedFib Nat.one))
    (fun n pair => Bool.rec (pair .true) ((shiftedFib n.succ.succ).add (pair .false))) k) .false

theorem alternatingSum_zero : Eq (alternatingSum .zero) Int.zero := Omega.rfl

theorem alternatingSum_one : Eq (alternatingSum Nat.one) (shiftedFib Nat.one) := Omega.rfl

theorem alternatingSum_add_two (k : Nat) :
    Eq (alternatingSum k.succ.succ) ((shiftedFib k.succ.succ).add (alternatingSum k)) := Omega.rfl

private theorem shiftedFib_add_two (k : Nat) :
    Eq (shiftedFib k.succ.succ.succ) ((shiftedFib k.succ).add (shiftedFib k.succ.succ)) :=
  congrArg Int.ofNat (Nat.fib_add_two (n := k.succ.succ))

private theorem sum_step (k : Nat)
    (ih : Eq (alternatingSum k) ((shiftedFib k.succ).sub Int.one)) :
    Eq (alternatingSum k.succ.succ) ((shiftedFib k.succ.succ.succ).sub Int.one) :=
  let a := shiftedFib k.succ.succ
  let b := shiftedFib k.succ
  (alternatingSum_add_two k).trans
    ((congrArg a.add (ih.trans Int.sub_eq_add_neg)).trans
      ((Int.add_assoc a b Int.one.neg).symm.trans
        ((congrArg (fun t : Int => t.add Int.one.neg) (Int.add_comm a b)).trans
          ((congrArg (fun t : Int => t.add Int.one.neg) (shiftedFib_add_two k).symm).trans
            Int.sub_eq_add_neg.symm))))

private theorem shiftedFib_one : Eq (shiftedFib Nat.one) Int.one :=
  congrArg Int.ofNat Nat.fib_two

private theorem shiftedFib_two : Eq (shiftedFib Nat.one.succ) Int.two :=
  congrArg Int.ofNat Omega.Arithmetic.WDigits.wValue_one

private theorem sum_zero :
    Eq (alternatingSum .zero) ((shiftedFib Nat.one).sub Int.one) :=
  alternatingSum_zero.trans
    ((congrArg (fun x : Int => x.sub Int.one) shiftedFib_one).trans (Int.sub_self Int.one)).symm

private theorem sum_one :
    Eq (alternatingSum Nat.one) ((shiftedFib Nat.one.succ).sub Int.one) :=
  (alternatingSum_one.trans shiftedFib_one).trans
    ((congrArg (fun x : Int => x.sub Int.one) shiftedFib_two).trans
      (Int.subNatNat_eq_coe.symm.trans
        ((congrArg (fun n : Nat => Int.subNatNat n Nat.one) (Nat.add_one Nat.one).symm).trans
          (Int.subNatNat_add_left (m := Nat.one) (n := Nat.one))))).symm

/-- The parity-descending sum is the next shifted Fibonacci number minus one. -/
theorem alternating_sum_eq (k : Nat) :
    Eq (alternatingSum k) ((shiftedFib k.succ).sub Int.one) :=
  (Nat.rec (motive := fun n => And
    (Eq (alternatingSum n) ((shiftedFib n.succ).sub Int.one))
    (Eq (alternatingSum n.succ) ((shiftedFib n.succ.succ).sub Int.one)))
    (And.intro sum_zero sum_one)
    (fun n ih => And.intro ih.right (sum_step n ih.left)) k).left

end Omega.Arithmetic.Fibonacci
