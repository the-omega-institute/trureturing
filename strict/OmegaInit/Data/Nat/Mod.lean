/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import OmegaInit.Core
import OmegaInit.Data.Nat.Basic
import OmegaInit.Data.Nat.Dvd
import OmegaInit.Data.Nat.Div.Lemmas

namespace Omega.Nat

public protected theorem mul_lt_mul_left {a b c : Nat} (a0 : Nat.lt zero a) :
    Iff (Nat.lt (Nat.mul a b) (Nat.mul a c)) (Nat.lt b c) :=
  Iff.intro (fun h => Nat.lt_of_not_ge fun ge => Nat.not_lt_of_ge (Nat.mul_le_mul_left a ge) h)
    (fun h => Nat.mul_lt_mul_of_pos_left h a0)

end Omega.Nat

port_proof Nat.mul_lt_mul_right by_constructive_casts
port_proof Nat.lt_of_mul_lt_mul_left by_constructive_casts
port_proof Nat.lt_of_mul_lt_mul_right by_constructive_casts

namespace Omega.Nat

public protected theorem div_lt_of_lt_mul {m n k : Nat} (h : Nat.lt m (Nat.mul n k)) :
    Nat.lt (Nat.div m n) k :=
  _root_.Omega.Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt (Nat.le_add_left _ _)
    (Eq.subst (motive := fun x => Nat.lt x (Nat.mul n k)) (Nat.mod_add_div m n).symm h))

end Omega.Nat

port_proof Nat.mod_mul_right_div_self by_constructive_casts
port_proof Nat.mod_mul_left_div_self by_constructive_casts
port_proof Nat.mod_mul_right_mod by_constructive_casts
port_proof Nat.mod_mul_left_mod by_constructive_casts
port_proof Nat.mod_mul by_constructive_casts
port_proof Nat.mod_pow_succ by_constructive_casts
port_proof Nat.two_pow_mod_two_eq_zero by_constructive_casts
port_proof Nat.two_pow_mod_two_eq_one by_constructive_casts

public section
namespace Nat
export _root_.Omega.Nat (mul_lt_mul_left mul_lt_mul_right lt_of_mul_lt_mul_left
  lt_of_mul_lt_mul_right div_lt_of_lt_mul mod_mul_right_div_self
  mod_mul_left_div_self mod_mul_right_mod mod_mul_left_mod
  mod_mul mod_pow_succ two_pow_mod_two_eq_zero
  two_pow_mod_two_eq_one)
end Nat
