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

theorem square_mul (a k : Nat) : Eq (Nat.mul (Nat.mul a k) (Nat.mul a k)) (Nat.mul (Nat.mul a a) (Nat.mul k k)) :=
  (Nat.mul_assoc (Nat.mul a k) a k).symm.trans
    ((congrArg (fun x => Nat.mul x k) (Nat.mul_right_comm a k a)).trans (Nat.mul_assoc (Nat.mul a a) k k))

end Omega.Nat

namespace Nat
export _root_.Omega.Nat (square_mul)
end Nat
