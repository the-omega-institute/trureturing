/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude

public import OmegaInit.Data.Nat.Lemmas
public import OmegaMathlib.Order.RelClasses

/-!
The strict counterparts of the Fibonacci sequence and its initial recurrence
and order lemmas from `Mathlib.Data.Nat.Fib.Basic`. The definition reuses the
iterator first implemented in `OmegaMath.Arithmetic.ContinuedFraction.Convergents`.
-/

noncomputable section

@[expose] public section


namespace Omega.Nat

/-- Fibonacci numbers computed by iterating consecutive pairs. -/
@[no_expose] def fib (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Bool → Nat) (Bool.rec zero zero.succ)
    (fun _ pair => Bool.rec (pair .true) ((pair .true).add (pair .false))) n .false

theorem fib_zero : Eq (fib zero) zero := Omega.rfl

theorem fib_one : Eq (fib zero.succ) zero.succ := Omega.rfl

theorem fib_two : Eq (fib zero.succ.succ) zero.succ := Omega.rfl

theorem fib_add_two {n : Nat} : Eq (fib n.succ.succ) ((fib n).add (fib n.succ)) :=
  Nat.add_comm (fib n.succ) (fib n)

theorem fib_le_fib_succ {n : Nat} : Nat.le (fib n) (fib n.succ) :=
  Nat.rec (motive := fun n => Nat.le (fib n) (fib n.succ)) (zero_le zero.succ)
    (fun n _ => Nat.add_le_add_left (zero_le (fib n)) (fib n.succ)) n

private theorem fib_succ_pos (n : Nat) : Nat.lt zero (fib n.succ) :=
  Nat.rec (motive := fun n => Nat.lt zero (fib n.succ)) (Nat.le_refl zero.succ)
    (fun _ ih => Nat.le_trans ih fib_le_fib_succ) n

theorem fib_pos {n : Nat} : Iff (Nat.lt zero (fib n)) (Nat.lt zero n) :=
  Nat.rec (motive := fun n => Iff (Nat.lt zero (fib n)) (Nat.lt zero n))
    (Iff.intro (fun h => h) (fun h => h))
    (fun n _ => Iff.intro (fun _ => succ_le_succ (zero_le n)) (fun _ => fib_succ_pos n)) n

theorem fib_lt_fib_succ {n : Nat} (hn : Nat.le zero.succ.succ n) : Nat.lt (fib n) (fib n.succ) :=
  (Nat.rec (motive := fun n => Nat.le zero.succ.succ n → Nat.lt (fib n) (fib n.succ))
    (fun h => False.elim (not_succ_le_zero zero.succ h))
    (fun n _ h => Nat.add_le_add_left ((fib_pos (n := n)).mpr (le_of_succ_le_succ h)) (fib n.succ)) n) hn

attribute [irreducible] fib

end Omega.Nat

public section
namespace Nat
export _root_.Omega.Nat (fib fib_add_two fib_le_fib_succ fib_lt_fib_succ fib_one fib_pos fib_two fib_zero)
end Nat
