/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Prelude
import OmegaInit.Data.Nat.Div.Basic
import all OmegaInit.Prelude

noncomputable section

@[expose] public section

namespace Omega.Nat

/-- A Euclidean step strictly decreases the first positive argument, so its successor
bounds the number of calls, including the final zero case. -/
@[no_expose] def gcd (m n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ b => b)
    (fun _ smaller a b => Nat.rec b (fun d _ => smaller (Nat.mod b (succ d)) (succ d)) a)
    (succ m) m n

attribute [local semireducible] Nat.mod Nat.ble Nat.sub Nat.pred

theorem gcd_zero_right (n : Nat) : Eq (gcd n zero) n :=
  Nat.rec (motive := fun m => Eq (gcd m zero) m) Omega.rfl (fun _ _ => Omega.rfl) n

theorem gcd_one_left (n : Nat) : Eq (gcd (succ zero) n) (succ zero) :=
  (congrArg (fun m => Nat.rec (motive := fun _ => Nat)
    (succ zero) (fun d _ => succ d) m) (mod_one n)).trans Omega.rfl

attribute [irreducible] gcd

end Omega.Nat
