/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
module
prelude
public import OmegaInit.Data.Nat.Gcd
import OmegaInit.Data.Nat.Dvd
import OmegaInit.PropLemmas
import OmegaInit.Data.Nat.Basic

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

port_proof Nat.Coprime.dvd_of_dvd_mul_right by_constructive_casts
port_proof Nat.Coprime.eq_1 by_constructive_casts
port_proof Nat.Coprime.symm by_constructive_casts
port_proof Nat.Coprime.dvd_of_dvd_mul_left by_constructive_casts
port_proof Nat.Coprime.gcd_mul_left_cancel by_constructive_casts
port_proof Nat.Coprime.mul_left by_constructive_casts
port_proof Nat.Coprime.coprime_dvd_left by_constructive_casts
port_proof Nat.Coprime.gcd_left by_constructive_casts
port_proof Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul by_constructive_casts
port_proof Nat.Coprime.coprime_dvd_right by_constructive_casts
port_proof Nat.Coprime.coprime_mul_right by_constructive_casts
port_proof Nat.Coprime.gcd_mul_left_cancel_right by_constructive_casts
port_proof Nat.Coprime.gcd_right by_constructive_casts
port_proof Nat.Coprime.coprime_mul_left by_constructive_casts
port_private_declaration Nat.coprime_mul_iff_left.match_1_1
port_proof Nat.coprime_mul_iff_left by_constructive_casts
port_proof Nat.coprime_comm by_constructive_casts
namespace Omega.Nat

theorem coprime_mul_iff_right {k m n : Nat} :
    Iff (Coprime k (Nat.mul m n)) (And (Coprime k m) (Coprime k n)) :=
  Iff.intro (fun h =>
    let both := coprime_mul_iff_left.mp (Coprime.symm h)
    And.intro (Coprime.symm both.left) (Coprime.symm both.right))
    (fun h => Coprime.symm (coprime_mul_iff_left.mpr (And.intro (Coprime.symm h.left) (Coprime.symm h.right))))

end Omega.Nat
port_proof Nat.coprime_div_gcd_div_gcd by_constructive_casts
namespace Omega.Nat

theorem exists_coprime (m n : Nat) :
    Exists (fun a => Exists (fun b => And (Coprime a b)
      (And (Eq m (Nat.mul a (gcd m n))) (Eq n (Nat.mul b (gcd m n)))))) :=
  Or.elim (eq_zero_or_pos (gcd m n))
    (fun e =>
      let z := gcd_eq_zero_iff.mp e
      Exists.intro (succ zero) (Exists.intro (succ zero) (And.intro (coprime_one_left _)
        (And.intro (z.left.trans (e.symm.trans (Nat.one_mul _).symm))
          (z.right.trans (e.symm.trans (Nat.one_mul _).symm))))))
    (fun pos => Exists.intro _ (Exists.intro _ (And.intro (coprime_div_gcd_div_gcd pos)
      (And.intro (Nat.div_mul_cancel (gcd_dvd_left m n)).symm (Nat.div_mul_cancel (gcd_dvd_right m n)).symm))))

end Omega.Nat
port_proof Nat.Coprime.coprime_mul_left_right by_constructive_casts
port_private_declaration Nat.Coprime.coprime_div_left.match_1_3
port_private_declaration Nat.Coprime.coprime_div_left.match_1_1
port_proof Nat.Coprime.coprime_div_left by_constructive_casts
port_proof Nat.Coprime.pow_left by_constructive_casts
port_proof Nat.coprime_self by_constructive_casts
port_proof Nat.Coprime.pow_right by_constructive_casts
port_proof Nat.Coprime.pow by_constructive_casts
port_proof Nat.Coprime.mul_right by_constructive_casts
port_proof Nat.Coprime.gcd_both by_constructive_casts
port_private_declaration Nat.Coprime.mul_dvd_of_dvd_of_dvd.match_1_1
port_proof Nat.Coprime.mul_dvd_of_dvd_of_dvd by_constructive_casts
port_proof Nat.Coprime.gcd_mul by_constructive_casts
port_proof Nat.Coprime.mul_gcd by_constructive_casts
port_proof Nat.Coprime.coprime_mul_right_right by_constructive_casts
port_proof Nat.Coprime.gcd_mul_right_cancel_right by_constructive_casts
port_proof Nat.Coprime.eq_one_of_dvd by_constructive_casts
port_proof Nat.not_coprime_of_dvd_of_dvd by_constructive_casts
port_proof Nat.Coprime.coprime_div_right by_constructive_casts
port_private_declaration Nat.exists_coprime'.match_1_1
port_proof Nat.exists_coprime' by_constructive_casts
port_proof Nat.Coprime.gcd_mul_right_cancel by_constructive_casts

namespace Nat
export _root_.Omega.Nat (coprime_comm coprime_div_gcd_div_gcd coprime_mul_iff_left
  coprime_mul_iff_right coprime_self exists_coprime exists_coprime'
  gcd_mul_gcd_of_coprime_of_mul_eq_mul not_coprime_of_dvd_of_dvd)
end Nat
