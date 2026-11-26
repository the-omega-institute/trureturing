/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Prelude

public section
namespace Omega.Nat

theorem mod_one (x : Nat) : Eq (Nat.mod x (succ zero)) zero :=
  Nat.le_antisymm (Nat.le_of_succ_le_succ (Nat.mod_lt x (Nat.le_refl (succ zero)))) (Nat.zero_le _)

end Omega.Nat
