/- GID: D5/S0/Conventions/CanonicalDigits
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The zero-based Fibonacci weights for canonical nonadjacent integer digits. -/

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude

public import D5.S0.Arithmetic.Exact.Nat
public import OmegaMathlib.Data.Nat.Fib.Basic

/-!
Omega original.

The zero-based Fibonacci weights for canonical nonadjacent integer digits.
-/

noncomputable section

@[expose] public section

namespace Omega.Arithmetic.WDigits

/-- The weight of zero-based W position `index` is `F_(index + 2)`. -/
def wValue (index : Nat) : Nat := Nat.fib index.succ.succ

theorem wValue_zero : Eq (wValue .zero) Nat.one := Nat.fib_two

private theorem one_add (n : Nat) : Eq (Nat.one.add n) n.succ :=
  (Nat.succ_add Nat.zero n).trans (congrArg Nat.succ (Nat.zero_add n))

theorem wValue_one : Eq (wValue Nat.one) Nat.one.succ :=
  Nat.fib_add_two.trans ((congrArg (fun x : Nat => x.add (Nat.fib Nat.one.succ)) Nat.fib_one).trans
    ((congrArg (Nat.add Nat.one) Nat.fib_two).trans (one_add Nat.one)))

theorem wValue_two : Eq (wValue Nat.one.succ) Nat.one.succ.succ :=
  Nat.fib_add_two.trans ((congrArg (fun x : Nat => x.add (wValue Nat.one)) Nat.fib_two).trans
    ((congrArg (Nat.add Nat.one) wValue_one).trans (one_add Nat.one.succ)))

theorem wValue_add_two (index : Nat) :
    Eq (wValue index.succ.succ) ((wValue index).add (wValue index.succ)) :=
  Nat.fib_add_two

theorem wValue_lt_succ (index : Nat) : Nat.lt (wValue index) (wValue index.succ) :=
  Nat.fib_lt_fib_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le index)))

/-- W position `n` has weight at least `n+1`, giving finite search bounds. -/
theorem succ_le_wValue (index : Nat) : Nat.le index.succ (wValue index) :=
  Nat.rec (motive := fun n => Nat.le n.succ (wValue n))
    (Eq.subst (motive := Nat.le Nat.one) wValue_zero.symm (Nat.le_refl Nat.one))
    (fun n ih => Nat.le_trans (Nat.succ_le_succ ih) (wValue_lt_succ n)) index

end Omega.Arithmetic.WDigits
