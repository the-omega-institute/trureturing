/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Data.Nat.Basic

@[expose] public section

namespace Omega.Nat

theorem mul_right_comm (a b c : Nat) : Eq (mul (mul a b) c) (mul (mul a c) b) :=
  (mul_assoc a b c).trans ((congrArg (mul a) (mul_comm b c)).trans (mul_assoc a c b).symm)

end Omega.Nat
