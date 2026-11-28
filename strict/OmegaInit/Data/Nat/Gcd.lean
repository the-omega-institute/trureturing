/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Prelude
public import OmegaInit.Data.Nat.Div.Basic
import all OmegaInit.Prelude
import OmegaInit.Data.Nat.Dvd
import OmegaInit.Data.Nat.Basic
import OmegaInit.WF

noncomputable section

@[expose] public section

namespace Omega.Nat

private def euclideanSteps : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ b => b)
    (fun _ smaller a b => Nat.rec b (fun d _ => smaller (Nat.mod b (succ d)) (succ d)) a)

/-- A Euclidean step strictly decreases the first positive argument, so its successor
bounds the number of calls, including the final zero case. -/
@[extern "lean_nat_gcd", no_expose] def _root_.Nat.gcd (m n : @& Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ b => b)
    (fun _ smaller a b => Nat.rec b (fun d _ => smaller (Nat.mod b (succ d)) (succ d)) a)
    (succ m) m n

export _root_.Nat (gcd)

theorem gcd_zero_right (n : Nat) : Eq (gcd n zero) n :=
  Nat.rec (motive := fun m => Eq (gcd m zero) m) Omega.rfl (fun _ _ => Omega.rfl) n

theorem gcd_one_left (n : Nat) : Eq (gcd (succ zero) n) (succ zero) :=
  (congrArg (fun m => Nat.rec (motive := fun _ => Nat)
    (succ zero) (fun d _ => succ d) m) (mod_one n)).trans Omega.rfl

private theorem steps_agree (fuel : Nat) : ∀ other a b, Nat.lt a fuel → Nat.lt a other →
    Eq (euclideanSteps fuel a b) (euclideanSteps other a b) :=
  Nat.rec (motive := fun f => ∀ g a b, Nat.lt a f → Nat.lt a g →
      Eq (euclideanSteps f a b) (euclideanSteps g a b))
    (fun _ a _ h _ => False.elim (not_succ_le_zero a h))
    (fun f ih g => Nat.casesOn (motive := fun g => ∀ a b, Nat.lt a (succ f) → Nat.lt a g →
        Eq (euclideanSteps (succ f) a b) (euclideanSteps g a b)) g
      (fun a _ _ h => False.elim (not_succ_le_zero a h))
      (fun g a => Nat.casesOn (motive := fun a => ∀ b, Nat.lt a (succ f) → Nat.lt a (succ g) →
          Eq (euclideanSteps (succ f) a b) (euclideanSteps (succ g) a b)) a
        (fun _ _ _ => Omega.rfl)
        (fun d b hf hg =>
          have smaller := Nat.mod_lt b (succ_le_succ (zero_le d))
          ih g (Nat.mod b (succ d)) (succ d)
            (Nat.le_trans smaller (le_of_succ_le_succ hf))
            (Nat.le_trans smaller (le_of_succ_le_succ hg))))) fuel

theorem gcd_zero_left (y : Nat) : Eq (gcd zero y) y := Omega.rfl

theorem gcd_succ (x y : Nat) : Eq (gcd (succ x) y) (gcd (Nat.mod y (succ x)) (succ x)) :=
  steps_agree (succ x) (succ (Nat.mod y (succ x))) (Nat.mod y (succ x)) (succ x)
    (Nat.mod_lt y (succ_le_succ (zero_le x))) (Nat.le_refl _)

theorem gcd_one_right (n : Nat) : Eq (gcd n (succ zero)) (succ zero) :=
  Nat.casesOn (motive := fun a => Eq (gcd a (succ zero)) (succ zero)) n
    (gcd_zero_left (succ zero))
    (fun k => Nat.casesOn (motive := fun a => Eq (gcd (succ a) (succ zero)) (succ zero)) k
      (gcd_one_left (succ zero))
      (fun j =>
        have lt : Nat.lt (succ zero) (succ (succ j)) := succ_le_succ (succ_le_succ (zero_le j))
        (gcd_succ (succ j) (succ zero)).trans
          ((congrArg (fun r => gcd r (succ (succ j))) (mod_eq_of_lt lt)).trans
            (gcd_one_left (succ (succ j))))))

theorem gcd_add_one (x y : Nat) : Eq (gcd (Nat.add x (succ zero)) y)
    (gcd (Nat.mod y (Nat.add x (succ zero))) (Nat.add x (succ zero))) := gcd_succ x y

theorem gcd_rec (m n : Nat) : Eq (gcd m n) (gcd (Nat.mod n m) m) :=
  Nat.casesOn (motive := fun m => Eq (gcd m n) (gcd (Nat.mod n m) m)) m
    ((gcd_zero_left n).trans ((gcd_zero_right n).symm.trans
      (congrArg (fun k => gcd k zero) (mod_zero n).symm)))
    (fun x => gcd_succ x n)

attribute [irreducible] gcd

end Omega.Nat

public section
namespace Nat
export _root_.Omega.Nat (gcd_add_one gcd_one_left gcd_one_right gcd_rec gcd_succ gcd_zero_left gcd_zero_right)
end Nat

port_private_declaration Nat.gcd.induction.match_1_1
port_proof Nat.gcd.induction by_constructive_casts
port_proof Nat.dvd_gcd by_constructive_casts
port_proof Nat.gcd_mul_left by_constructive_casts
port_proof Nat.gcd_dvd by_constructive_casts
port_proof Nat.gcd_dvd_right by_constructive_casts
port_proof Nat.gcd_mul_left_left by_constructive_casts
port_proof Nat.gcd_mul_right_left by_constructive_casts
port_proof Nat.gcd_dvd_left by_constructive_casts
port_proof Nat.gcd_comm by_constructive_casts
port_proof Nat.gcd_mul_right_right by_constructive_casts
port_proof Nat.gcd_dvd_gcd_of_dvd_left by_constructive_casts
port_proof Nat.gcd_dvd_gcd_mul_left_left by_constructive_casts
port_proof Nat.gcd_assoc by_constructive_casts
port_private_declaration Nat.dvdProdDvdOfDvdProd._proof_5
port_private_declaration Nat.dvdProdDvdOfDvdProd._proof_3
port_private_declaration Nat.eq_zero_of_gcd_eq_zero_left.match_1_1
port_proof Nat.gcd_pos_of_pos_left by_constructive_casts
port_proof Nat.eq_zero_of_gcd_eq_zero_left by_constructive_casts
port_proof Nat.eq_zero_of_gcd_eq_zero_right by_constructive_casts
port_private_declaration Nat.dvdProdDvdOfDvdProd._proof_1
port_private_declaration Nat.dvdProdDvdOfDvdProd._proof_2
port_proof Nat.gcd_mul_right by_constructive_casts
port_private_declaration Nat.dvdProdDvdOfDvdProd._proof_4
port_definition Nat.dvdProdDvdOfDvdProd with_native_code
port_private_declaration Nat.gcd_mul_right_dvd_mul_gcd.match_1_1
port_proof Nat.gcd_mul_right_dvd_mul_gcd by_constructive_casts
port_proof Nat.gcd_self by_constructive_casts
port_private_declaration Nat.gcd_div.match_1_1
port_proof Nat.gcd_div by_constructive_casts
port_proof Nat.gcd_eq_zero_iff by_constructive_casts
port_proof Nat.gcd_dvd_gcd_of_dvd_right by_constructive_casts
port_proof Nat.gcd_dvd_gcd_mul_left_right by_constructive_casts
port_proof Nat.gcd_dvd_gcd_mul_right_right by_constructive_casts
port_proof Nat.gcd_eq_left by_constructive_casts

namespace Nat
export _root_.Omega.Nat (dvdProdDvdOfDvdProd dvd_gcd eq_zero_of_gcd_eq_zero_left
  eq_zero_of_gcd_eq_zero_right gcd_assoc gcd_comm gcd_div gcd_dvd gcd_dvd_gcd_mul_left_left
  gcd_dvd_gcd_mul_left_right gcd_dvd_gcd_mul_right_right gcd_dvd_gcd_of_dvd_left
  gcd_dvd_gcd_of_dvd_right gcd_dvd_left gcd_dvd_right gcd_eq_left gcd_eq_zero_iff gcd_mul_left
  gcd_mul_left_left gcd_mul_right gcd_mul_right_dvd_mul_gcd gcd_mul_right_left gcd_mul_right_right
  gcd_pos_of_pos_left gcd_self)
end Nat

namespace Nat.gcd
export _root_.Omega.Nat.gcd (induction)
end Nat.gcd

port_proof Nat.gcd_mul_left_right by_constructive_casts
port_private_declaration Nat.dvd_gcd_iff.match_1_1
port_private_declaration Nat.dvd_gcd_iff.match_1_3
port_proof Nat.dvd_gcd_iff by_constructive_casts
port_proof Nat.gcd_right_eq_iff by_constructive_casts
port_proof Nat.gcd_mul_right_sub_right by_constructive_casts
port_proof Nat.gcd_mul_right_sub_left by_constructive_casts
port_proof Nat.gcd_self_sub_left by_constructive_casts
port_private_declaration Nat.dvd_gcd_mul_iff_dvd_mul.match_1_1
port_proof Nat.dvd_gcd_mul_iff_dvd_mul by_constructive_casts
port_proof Nat.dvd_mul_gcd_iff_dvd_mul by_constructive_casts
port_proof Nat.gcd_pos_of_pos_right by_constructive_casts
port_proof Nat.gcd_div_gcd_div_gcd_of_pos_right by_constructive_casts
port_proof Nat.instLawfulIdentityGcdOfNat by_constructive_casts
port_private_declaration Nat.gcd._unary._proof_1
port_definition Nat.gcd._unary
port_proof Nat.gcd_eq_iff by_constructive_casts
namespace Omega.Nat

theorem gcd_eq_one_iff {m n : Nat} : Iff (Eq (gcd m n) (succ zero))
    (∀ c, Dvd.dvd c m → Dvd.dvd c n → Eq c (succ zero)) :=
  Iff.intro (fun eq c hm hn =>
      eq_one_of_dvd_one (Eq.subst (motive := Dvd.dvd c) eq (dvd_gcd hm hn)))
    (fun h => h _ (gcd_dvd_left m n) (gcd_dvd_right m n))

end Omega.Nat
port_alternative_proof Nat.gcd_mul_right_right_of_gcd_eq_one from OmegaChecks.InitPort.Alternatives.Powers
port_proof Nat.gcd_mul_right_left_of_gcd_eq_one by_constructive_casts
port_proof Nat.gcd_mul_left_left_of_gcd_eq_one by_constructive_casts
port_proof Nat.gcd_pow_left_of_gcd_eq_one by_constructive_casts
port_proof Nat.gcd_pow_right_of_gcd_eq_one by_constructive_casts
port_proof Nat.pow_gcd_pow_of_gcd_eq_one by_constructive_casts
port_proof Nat.gcd_div_gcd_div_gcd_of_pos_left by_constructive_casts
port_proof Nat.pow_gcd_pow by_constructive_casts
port_proof Nat.gcd_add_mul_right_right by_constructive_casts
port_proof Nat.gcd_add_mul_right_left by_constructive_casts
port_proof Nat.gcd_add_mul_left_left by_constructive_casts
port_proof Nat.gcd_mul_left_add_left by_constructive_casts
port_proof Nat.gcd_mul_right_add_left by_constructive_casts
port_proof Nat.gcd_def by_constructive_casts
port_proof Nat.gcd_gcd_self_right_left by_constructive_casts
port_proof Nat.gcd_gcd_self_right_right by_constructive_casts
port_proof Nat.gcd_gcd_self_left_right by_constructive_casts
port_proof Nat.gcd_gcd_self_left_left by_constructive_casts
port_proof Nat.gcd_sub_mul_right_right by_constructive_casts
port_proof Nat.gcd_sub_mul_right_left by_constructive_casts
port_proof Nat.gcd_sub_self_left by_constructive_casts
port_proof Nat.gcd_self_add_left by_constructive_casts
port_proof Nat.gcd_left_eq_iff by_constructive_casts
port_proof Nat.gcd_eq_left_iff_dvd by_constructive_casts
port_proof Nat.gcd_eq_right_iff_dvd by_constructive_casts
port_proof Nat.gcd_mul_left_sub_left by_constructive_casts
port_proof Nat.gcd_left_comm by_constructive_casts
port_proof Nat.gcd_ne_zero_left by_constructive_casts
port_proof Nat.gcd_mul_left_sub_right by_constructive_casts
port_proof Nat.gcd_sub_left_right_of_dvd by_constructive_casts
port_proof Nat.instAssociativeGcd by_constructive_casts
port_proof Nat.gcd_add_mul_left_right by_constructive_casts
port_proof Nat.gcd_self_sub_right by_constructive_casts
port_proof Nat.gcd_mul_right_add_right by_constructive_casts
port_proof Nat.gcd_self_add_right by_constructive_casts
port_proof Nat.gcd_add_right_left_of_dvd by_constructive_casts
port_proof Nat.gcd_le_left by_constructive_casts
port_proof Nat.div_gcd_pos_of_pos_left by_constructive_casts
port_proof Nat.instCommutativeGcd by_constructive_casts
port_proof Nat.gcd_dvd_gcd_mul_right_left by_constructive_casts
port_proof Nat.gcd_sub_left_left_of_dvd by_constructive_casts
port_proof Nat.gcd_mul_left_dvd_mul_gcd by_constructive_casts
port_proof Nat.gcd_sub_mul_left_right by_constructive_casts
port_proof Nat.gcd_sub_right_right_of_dvd by_constructive_casts
port_proof Nat.gcd_sub_self_right by_constructive_casts
port_proof Nat.gcd_ne_zero_right by_constructive_casts
port_proof Nat.instIdempotentOpGcd by_constructive_casts
port_proof Nat.gcd_mul_left_add_right by_constructive_casts
port_proof Nat.gcd_add_left_right_of_dvd by_constructive_casts
port_proof Nat.gcd_eq_right by_constructive_casts
port_proof Nat.gcd_add_right_right_of_dvd by_constructive_casts
port_proof Nat.dvd_mul by_constructive_casts
namespace Omega.Nat

theorem gcd_pos_iff {m n : Nat} : Iff (Nat.lt zero (gcd m n)) (Or (Nat.lt zero m) (Nat.lt zero n)) :=
  Iff.intro (fun pos => Or.elim (eq_zero_or_pos m)
    (fun mz => Or.inr (zero_lt_of_ne_zero (fun nz =>
      Nat.not_lt_zero _ (Eq.subst (motive := Nat.lt zero) (gcd_eq_zero_iff.mpr (And.intro mz nz)) pos))))
    Or.inl)
    (fun h => Or.elim h (fun hm => gcd_pos_of_pos_left n hm)
      (fun hn => Eq.subst (motive := Nat.lt zero) (gcd_comm n m) (gcd_pos_of_pos_left m hn)))

end Omega.Nat
port_proof Nat.gcd_le_right by_constructive_casts
port_proof Nat.gcd_sub_mul_left_left by_constructive_casts
port_proof Nat.gcd_sub_right_left_of_dvd by_constructive_casts
port_alternative_proof Nat.pow_dvd_pow_iff from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.gcd_add_left_left_of_dvd by_constructive_casts
port_proof Nat.div_gcd_pos_of_pos_right by_constructive_casts
port_proof Nat.gcd_mul_left_right_of_gcd_eq_one by_constructive_casts
port_proof Nat.gcd_add_self_left by_constructive_casts
port_proof Nat.dvd_gcd_mul_gcd_iff_dvd_mul by_constructive_casts
port_proof Nat.gcd_add_self_right by_constructive_casts

namespace Nat
export _root_.Omega.Nat (div_gcd_pos_of_pos_left div_gcd_pos_of_pos_right dvd_gcd_iff
  dvd_gcd_mul_gcd_iff_dvd_mul dvd_gcd_mul_iff_dvd_mul dvd_mul dvd_mul_gcd_iff_dvd_mul
  gcd_add_left_left_of_dvd gcd_add_left_right_of_dvd gcd_add_mul_left_left gcd_add_mul_left_right
  gcd_add_mul_right_left gcd_add_mul_right_right gcd_add_right_left_of_dvd
  gcd_add_right_right_of_dvd gcd_add_self_left gcd_add_self_right gcd_def
  gcd_div_gcd_div_gcd_of_pos_left gcd_div_gcd_div_gcd_of_pos_right gcd_dvd_gcd_mul_right_left
  gcd_eq_iff gcd_eq_left_iff_dvd gcd_eq_one_iff gcd_eq_right gcd_eq_right_iff_dvd
  gcd_gcd_self_left_left gcd_gcd_self_left_right gcd_gcd_self_right_left gcd_gcd_self_right_right
  gcd_le_left gcd_le_right gcd_left_comm gcd_left_eq_iff gcd_mul_left_add_left
  gcd_mul_left_add_right gcd_mul_left_dvd_mul_gcd gcd_mul_left_left_of_gcd_eq_one gcd_mul_left_right
  gcd_mul_left_right_of_gcd_eq_one gcd_mul_left_sub_left gcd_mul_left_sub_right
  gcd_mul_right_add_left gcd_mul_right_add_right gcd_mul_right_left_of_gcd_eq_one
  gcd_mul_right_right_of_gcd_eq_one gcd_mul_right_sub_left gcd_mul_right_sub_right gcd_ne_zero_left
  gcd_ne_zero_right gcd_pos_iff gcd_pos_of_pos_right gcd_pow_left_of_gcd_eq_one
  gcd_pow_right_of_gcd_eq_one gcd_right_eq_iff gcd_self_add_left gcd_self_add_right
  gcd_self_sub_left gcd_self_sub_right gcd_sub_left_left_of_dvd gcd_sub_left_right_of_dvd
  gcd_sub_mul_left_left gcd_sub_mul_left_right gcd_sub_mul_right_left gcd_sub_mul_right_right
  gcd_sub_right_left_of_dvd gcd_sub_right_right_of_dvd gcd_sub_self_left gcd_sub_self_right
  instAssociativeGcd instCommutativeGcd instIdempotentOpGcd instLawfulIdentityGcdOfNat
  pow_dvd_pow_iff pow_gcd_pow pow_gcd_pow_of_gcd_eq_one)
end Nat

attribute [instance] Omega.Nat.instLawfulIdentityGcdOfNat Omega.Nat.instIdempotentOpGcd
  Omega.Nat.instCommutativeGcd Omega.Nat.instAssociativeGcd
