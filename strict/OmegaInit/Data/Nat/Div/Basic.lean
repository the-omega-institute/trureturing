/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Prelude
import all OmegaInit.Prelude

public section
namespace Omega.Nat

attribute [local semireducible] Nat.mod

theorem mod_zero (a : Nat) : Eq (Nat.mod a zero) a :=
  Nat.rec (motive := fun k => Eq (Nat.mod k zero) k) Omega.rfl (fun _ _ => Omega.rfl) a

theorem mod_one (x : Nat) : Eq (Nat.mod x (succ zero)) zero :=
  Nat.le_antisymm (Nat.le_of_succ_le_succ (Nat.mod_lt x (Nat.le_refl (succ zero)))) (Nat.zero_le _)

end Omega.Nat
