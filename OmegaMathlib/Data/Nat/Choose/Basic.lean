/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Data.Nat.Lemmas

/-!
The strict binomial coefficient and its computation rules from
`Mathlib.Data.Nat.Choose.Basic`.
-/

noncomputable section
@[expose] public section

namespace Omega.Nat

/-- Binomial coefficients computed by Pascal's recurrence. -/
@[no_expose] def choose : Nat → Nat → Nat := fun upper lower =>
  Nat.rec (motive := fun _ => Nat → Nat) (Nat.rec zero.succ (fun _ _ => zero))
    (fun _ previous => Nat.rec zero.succ (fun k _ => (previous k).add (previous k.succ)))
    upper lower

theorem choose_zero_right (n : Nat) : Eq (choose n zero) zero.succ :=
  Nat.rec (motive := fun n => Eq (choose n zero) zero.succ) rfl (fun _ _ => rfl) n

theorem choose_zero_succ (k : Nat) : Eq (choose zero k.succ) zero :=
  Omega.rfl

theorem choose_succ_succ (n k : Nat) :
    Eq (choose n.succ k.succ) ((choose n k).add (choose n k.succ)) :=
  Omega.rfl

attribute [irreducible] choose

end Omega.Nat

public section
namespace Nat
export _root_.Omega.Nat (choose choose_succ_succ choose_zero_right choose_zero_succ)
end Nat
