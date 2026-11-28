/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import OmegaInit.Core
import OmegaInit.Data.Nat.Basic
import OmegaInit.WF

namespace Omega.Nat

private theorem decrease {n p : Nat} (hp : Nat.lt 0 p) (hn : Nat.lt p n) :
    Nat.lt (Nat.sub n (Nat.mul p 2)) (Nat.sub n p) :=
  Eq.subst (motive := fun x => Nat.lt x (Nat.sub n p))
    ((congrArg (Nat.sub n) (Nat.mul_two p)).trans (Nat.sub_add_eq n p p)).symm
    (Nat.sub_lt (Nat.zero_lt_sub_of_lt hn) hp)

end Omega.Nat
port_proof Nat.nextPowerOfTwo_dec using Omega.Nat.decrease
port_private_declaration Nat.nextPowerOfTwo._proof_1
port_private_declaration Nat.nextPowerOfTwo.go._unary._proof_1
port_private_declaration Nat.nextPowerOfTwo.go._unary._proof_2
port_private_declaration Nat.nextPowerOfTwo.go._unary
port_private_declaration Nat.nextPowerOfTwo.go
port_definition Nat.nextPowerOfTwo with_native_code
port_definition Nat.isPowerOfTwo
port_proof Nat.isPowerOfTwo_one
port_private_declaration Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo.match_1_1
port_proof Nat.isPowerOfTwo_mul_two_of_isPowerOfTwo by_constructive_casts
port_private_declaration Nat.pos_of_isPowerOfTwo.match_1_1
port_proof Nat.pos_of_isPowerOfTwo by_constructive_casts

public section
namespace Nat
export _root_.Omega.Nat (isPowerOfTwo isPowerOfTwo_mul_two_of_isPowerOfTwo isPowerOfTwo_one nextPowerOfTwo nextPowerOfTwo_dec pos_of_isPowerOfTwo)
end Nat

/- Nat.isPowerOfTwo_one._simp_1 needs eq_true to turn the proof into equality with True.
The partial runtime helper Nat.nextPowerOfTwo.go._unsafe_rec is replaced by compiled fuel
recursion on WellFounded.Nat.fix.go. -/
