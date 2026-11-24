/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude

public import OmegaInit.Data.Nat.Lemmas

/-!
Omega original.

Natural-number helpers for exact ratios and homogeneous coordinates.
-/

@[expose] public section

namespace Omega.Nat

def one : Nat := succ zero

theorem square_mul (a k : Nat) : Eq (mul (mul a k) (mul a k)) (mul (mul a a) (mul k k)) :=
  (mul_assoc (mul a k) a k).symm.trans
    ((congrArg (fun x => mul x k) (mul_right_comm a k a)).trans (mul_assoc (mul a a) k k))

end Omega.Nat
