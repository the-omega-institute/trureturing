/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaMath.Data.Nat.Fib.Basic

/-!
Omega original.

The zero-based Fibonacci weights used by the W-coordinate system of
`D5.S0.Conventions.WDigits`.
-/

noncomputable section

@[expose] public section

namespace Omega.Arithmetic.WDigits

/-- The weight of zero-based W position `index` is `F_(index + 2)`. -/
def wValue (index : Nat) : Nat := Nat.fib index.succ.succ

theorem wValue_zero : Eq (wValue .zero) Nat.one := Eq.refl

theorem wValue_one : Eq (wValue Nat.one) Nat.one.succ := Eq.refl

theorem wValue_two : Eq (wValue Nat.one.succ) Nat.one.succ.succ := Eq.refl

theorem wValue_add_two (index : Nat) :
    Eq (wValue index.succ.succ) ((wValue index).add (wValue index.succ)) :=
  Nat.fib_add_two

theorem wValue_lt_succ (index : Nat) : Nat.lt (wValue index) (wValue index.succ) :=
  Nat.fib_lt_fib_succ (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le index)))

/-- W position `n` has weight at least `n+1`, giving finite search bounds. -/
theorem succ_le_wValue (index : Nat) : Nat.le index.succ (wValue index) :=
  Nat.rec (motive := fun n => Nat.le n.succ (wValue n)) (Nat.le.refl Nat.one)
    (fun n ih => Nat.le_trans (Nat.succ_le_succ ih) (wValue_lt_succ n)) index

end Omega.Arithmetic.WDigits
