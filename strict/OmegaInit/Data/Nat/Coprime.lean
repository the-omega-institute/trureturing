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

theorem coprime_one_right : ∀ n, Coprime n (succ zero) := gcd_one_right

theorem coprime_zero_left (n : Nat) : Iff (Coprime zero n) (Eq n (succ zero)) :=
  Iff.intro (fun h => (gcd_zero_left n).symm.trans h) (fun h => (gcd_zero_left n).trans h)

theorem coprime_zero_right (n : Nat) : Iff (Coprime n zero) (Eq n (succ zero)) :=
  Iff.intro (fun h => (gcd_zero_right n).symm.trans h) (fun h => (gcd_zero_right n).trans h)

/- The official coprime_one_left_eq_true and coprime_one_right_eq_true identify
the proposition with True. Each full rule is equivalent to ((1 : Nat) = 1) = True. -/
private theorem coprime_one_left_eq_true_iff :
    Iff (∀ n, Eq (Coprime (succ zero) n) True) (Eq (Eq (succ zero) (succ zero)) True) :=
  Iff.intro (fun h => (congrArg (fun k => Eq k (succ zero)) (gcd_one_left zero)).symm.trans (h zero))
    (fun tag n => (congrArg (fun k => Eq k (succ zero)) (gcd_one_left n)).trans tag)

private theorem coprime_one_right_eq_true_iff :
    Iff (∀ n, Eq (Coprime n (succ zero)) True) (Eq (Eq (succ zero) (succ zero)) True) :=
  Iff.intro (fun h => (congrArg (fun k => Eq k (succ zero)) (gcd_zero_left (succ zero))).symm.trans (h zero))
    (fun tag n => (congrArg (fun k => Eq k (succ zero)) (gcd_one_right n)).trans tag)

end Omega.Nat

port_proof Nat.instDecidableCoprime._proof_1 by_constructive_casts
port_definition Nat.instDecidableCoprime with_native_code
port_proof Nat.coprime_iff_gcd_eq_one by_reflexivity
port_proof Nat.Coprime.gcd_eq_one

public section
namespace Nat
export _root_.Omega.Nat (Coprime instDecidableCoprime coprime_iff_gcd_eq_one coprime_one_left coprime_one_right
  coprime_zero_left coprime_zero_right)
end Nat
