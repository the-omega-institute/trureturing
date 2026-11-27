/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Nat.Gcd

@[expose] public section
namespace Omega.Nat

@[reducible] def Coprime (m n : Nat) : Prop := Eq (gcd m n) (succ zero)

theorem coprime_one_left : ∀ n, Coprime (succ zero) n := gcd_one_left

end Omega.Nat

public section
namespace Nat
export _root_.Omega.Nat (Coprime coprime_one_left)
end Nat
