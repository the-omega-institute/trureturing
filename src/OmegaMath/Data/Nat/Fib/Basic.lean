/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaMath.Data.Nat

/-!
The strict counterparts of the Fibonacci sequence and its initial recurrence
and order lemmas from `Mathlib.Data.Nat.Fib.Basic`. The definition reuses the
iterator first implemented in `OmegaMath.Arithmetic.ContinuedFraction.Convergents`.
-/

noncomputable section

@[expose] public section

namespace Omega.Nat

/-- Fibonacci numbers computed by iterating consecutive pairs. -/
def fib (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Bool → Nat) (Bool.rec zero one)
    (fun _ pair => Bool.rec (pair .true) ((pair .true).add (pair .false))) n .false

theorem fib_zero : Eq (fib zero) zero := Eq.refl

theorem fib_one : Eq (fib one) one := Eq.refl

theorem fib_two : Eq (fib one.succ) one := Eq.refl

theorem fib_add_two {n : Nat} : Eq (fib n.succ.succ) ((fib n).add (fib n.succ)) :=
  add_comm (fib n.succ) (fib n)

theorem fib_le_fib_succ {n : Nat} : le (fib n) (fib n.succ) :=
  Nat.rec (motive := fun n => le (fib n) (fib n.succ)) (zero_le one)
    (fun n _ => add_le_add_left (zero_le (fib n)) (fib n.succ)) n

private theorem fib_succ_pos (n : Nat) : lt zero (fib n.succ) :=
  Nat.rec (motive := fun n => lt zero (fib n.succ)) (le.refl one)
    (fun _ ih => le_trans ih fib_le_fib_succ) n

theorem fib_pos {n : Nat} : Iff (lt zero (fib n)) (lt zero n) :=
  Nat.rec (motive := fun n => Iff (lt zero (fib n)) (lt zero n))
    (Iff.intro (fun h => h) (fun h => h))
    (fun n _ => Iff.intro (fun _ => zero_le n) (fun _ => fib_succ_pos n)) n

theorem fib_lt_fib_succ {n : Nat} (hn : le one.succ n) : lt (fib n) (fib n.succ) :=
  (Nat.rec (motive := fun n => le one.succ n → lt (fib n) (fib n.succ))
    (fun h => False.elim h)
    (fun n _ h => add_le_add_left ((fib_pos (n := n)).mpr h) (fib n.succ)) n) hn

end Omega.Nat
