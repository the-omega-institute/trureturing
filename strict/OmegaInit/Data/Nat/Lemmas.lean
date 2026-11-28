/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude

public import OmegaInit.Data.Nat.Basic
public import OmegaInit.Data.Nat.Div.Basic
public import OmegaInit.Data.Nat.Log2
public import OmegaInit.PropLemmas
public import OmegaInit.Data.Nat.Bitwise.Basic
import all OmegaInit.Data.Nat.Bitwise.Basic
import OmegaInit.Data.Nat.Dvd
import OmegaInit.Data.Nat.MinMax
import OmegaInit.Data.Nat.Mod

@[expose] public section


namespace Omega.Nat

protected theorem mul_right_comm (n m k : Nat) : Eq (Nat.mul (Nat.mul n m) k) (Nat.mul (Nat.mul n k) m) :=
  (Nat.mul_assoc n m k).trans ((congrArg (Nat.mul n) (Nat.mul_comm m k)).trans (Nat.mul_assoc n k m).symm)

theorem mul_eq_zero {m n : Nat} : Iff (Eq (Nat.mul n m) zero) (Or (Eq n zero) (Eq m zero)) :=
  Iff.intro
    (Nat.rec (motive := fun m => Eq (Nat.mul n m) zero → Or (Eq n zero) (Eq m zero))
      (fun _ => Or.inr rfl)
      (fun _ _ h => Or.inl (eq_zero_of_add_eq_zero h).right) m)
    (fun h => h.elim
      (fun ha => Eq.subst (motive := fun n => Eq (Nat.mul n m) zero) ha.symm (Nat.zero_mul m))
      (fun hb => Eq.subst (motive := fun m => Eq (Nat.mul n m) zero) hb.symm rfl))

protected theorem sub_one (n : Nat) :
    Eq (Nat.sub n zero.succ) (pred n) :=
  Omega.rfl

theorem one_add (n : Nat) :
    Eq (Nat.add zero.succ n) (succ n) :=
  Nat.add_comm zero.succ n

theorem succ_ne_succ {m n : Nat} :
    Iff (Ne (succ m) (succ n)) (Ne m n) :=
  succ_ne_succ_iff

theorem one_lt_succ_succ (n : Nat) :
    Nat.lt zero.succ (succ (succ n)) :=
  succ_lt_succ (succ_le_succ (zero_le n))

theorem succ_le {n m : Nat} :
    Iff (Nat.le (succ n) m) (Nat.lt n m) :=
  Iff.rfl

theorem lt_iff_add_one_le {m n : Nat} :
    Iff (Nat.lt m n) (Nat.le (Nat.add m zero.succ) n) :=
  Iff.rfl

theorem lt_one_add_iff {m n : Nat} :
    Iff (Nat.lt m (Nat.add zero.succ n)) (Nat.le m n) :=
  Eq.subst (motive := fun x => Iff (Nat.lt m x) (Nat.le m n)) (one_add n).symm Nat.lt_succ_iff

theorem one_add_le_iff {m n : Nat} :
    Iff (Nat.le (Nat.add zero.succ m) n) (Nat.lt m n) :=
  Eq.subst (motive := fun x => Iff (Nat.le x n) (Nat.lt m n)) (one_add m).symm Iff.rfl

theorem one_le_of_lt {a b : Nat} (h : Nat.lt a b) :
    Nat.le zero.succ b :=
  Nat.le_trans (succ_le_succ (zero_le a)) h

theorem pred_one_add (n : Nat) :
    Eq (pred (Nat.add zero.succ n)) n :=
  congrArg pred (one_add n)

theorem pred_eq_of_eq_succ {m n : Nat} (H : Eq m (succ n)) :
    Eq (pred m) n :=
  congrArg pred H

theorem add_succ_sub_one (m n : Nat) :
    Eq (Nat.sub (Nat.add m (succ n)) zero.succ) (Nat.add m n) :=
  Omega.rfl

theorem succ_add_sub_one (n m : Nat) :
    Eq (Nat.sub (Nat.add (succ m) n) zero.succ) (Nat.add m n) :=
  congrArg pred (succ_add m n)

theorem pred_sub (n m : Nat) :
    Eq (Nat.sub (pred n) m) (pred (Nat.sub n m)) :=
  Nat.rec (motive := fun m => Eq (Nat.sub (pred n) m) (pred (Nat.sub n m)))
    Omega.rfl (fun _ ih => congrArg pred ih) m

protected theorem add_add_add_comm (a b c d : Nat) :
    Eq (Nat.add (Nat.add a b) (Nat.add c d)) (Nat.add (Nat.add a c) (Nat.add b d)) :=
  (Nat.add_assoc a b (Nat.add c d)).trans ((congrArg (Nat.add a) (Nat.add_left_comm b c d)).trans
    (Nat.add_assoc a c (Nat.add b d)).symm)

theorem succ_eq_one_add (n : Nat) :
    Eq (succ n) (Nat.add zero.succ n) :=
  (one_add n).symm

theorem succ_add_eq_add_succ (a b : Nat) :
    Eq (Nat.add (succ a) b) (Nat.add a (succ b)) :=
  succ_add a b

protected theorem eq_zero_of_add_eq_zero_right {n m : Nat} (h : Eq (Nat.add n m) zero) :
    Eq n zero :=
  (eq_zero_of_add_eq_zero h).left

protected theorem add_eq_zero_iff {n m : Nat} :
    Iff (Eq (Nat.add n m) zero) (And (Eq n zero) (Eq m zero)) :=
  Iff.intro eq_zero_of_add_eq_zero
    (fun h => (congrArg (fun x => Nat.add x m) h.left).trans ((Nat.zero_add m).trans h.right))

protected theorem add_left_cancel_iff {m k n : Nat} :
    Iff (Eq (Nat.add n m) (Nat.add n k)) (Eq m k) :=
  Iff.intro Nat.add_left_cancel (congrArg (Nat.add n))

protected theorem add_right_cancel_iff {m k n : Nat} :
    Iff (Eq (Nat.add m n) (Nat.add k n)) (Eq m k) :=
  Iff.intro Nat.add_right_cancel (congrArg (fun x => Nat.add x n))

protected theorem add_left_inj {m k n : Nat} :
    Iff (Eq (Nat.add m n) (Nat.add k n)) (Eq m k) :=
  Nat.add_right_cancel_iff

protected theorem add_right_inj {m k n : Nat} :
    Iff (Eq (Nat.add n m) (Nat.add n k)) (Eq m k) :=
  Nat.add_left_cancel_iff

protected theorem add_eq_left {a b : Nat} :
    Iff (Eq (Nat.add a b) a) (Eq b zero) :=
  Iff.intro (fun h => @Nat.add_left_cancel a b zero h) (congrArg (Nat.add a))

protected theorem add_eq_right {a b : Nat} :
    Iff (Eq (Nat.add a b) b) (Eq a zero) :=
  Iff.intro (fun h => Nat.add_right_cancel (h.trans (Nat.zero_add b).symm))
    (fun h => (congrArg (fun x => Nat.add x b) h).trans (Nat.zero_add b))

protected theorem left_eq_add {a b : Nat} :
    Iff (Eq a (Nat.add a b)) (Eq b zero) :=
  Iff.intro (fun h => Nat.add_eq_left.mp h.symm) (fun h => (Nat.add_eq_left.mpr h).symm)

protected theorem right_eq_add {a b : Nat} :
    Iff (Eq b (Nat.add a b)) (Eq a zero) :=
  Iff.intro (fun h => Nat.add_eq_right.mp h.symm) (fun h => (Nat.add_eq_right.mpr h).symm)

protected theorem sub_right_comm (m n k : Nat) :
    Eq (Nat.sub (Nat.sub m n) k) (Nat.sub (Nat.sub m k) n) :=
  (Nat.sub_sub m n k).trans ((congrArg (Nat.sub m) (Nat.add_comm n k)).trans (Nat.sub_sub m k n).symm)

protected theorem add_sub_cancel_right (n m : Nat) :
    Eq (Nat.sub (Nat.add n m) m) n :=
  Nat.add_sub_cancel n m

theorem succ_sub_one (n : Nat) :
    Eq (Nat.sub (succ n) zero.succ) n :=
  Omega.rfl

protected theorem one_add_sub_one (n : Nat) :
    Eq (Nat.sub (Nat.add zero.succ n) zero.succ) n :=
  pred_one_add n

theorem sub_succ' (m n : Nat) :
    Eq (Nat.sub m (succ n)) (Nat.sub (Nat.sub m n) zero.succ) :=
  Omega.rfl

protected theorem pow_two (a : Nat) :
    Eq (Nat.pow a zero.succ.succ) (Nat.mul a a) :=
  congrArg (fun x => Nat.mul x a) (Nat.pow_one a)

protected theorem one_pow (n : Nat) :
    Eq (Nat.pow zero.succ n) zero.succ :=
  Nat.rec (motive := fun k => Eq (Nat.pow zero.succ k) zero.succ)
    Omega.rfl (fun k ih => (Nat.mul_one (Nat.pow zero.succ k)).trans ih) n

theorem pow_succ' {m n : Nat} :
    Eq (Nat.pow m (succ n)) (Nat.mul m (Nat.pow m n)) :=
  Nat.mul_comm (Nat.pow m n) m

theorem pow_add_one' {m n : Nat} :
    Eq (Nat.pow m (Nat.add n zero.succ)) (Nat.mul m (Nat.pow m n)) :=
  pow_succ'

protected theorem pow_add (a m n : Nat) :
    Eq (Nat.pow a (Nat.add m n)) (Nat.mul (Nat.pow a m) (Nat.pow a n)) :=
  Nat.rec (motive := fun k => Eq (Nat.pow a (Nat.add m k)) (Nat.mul (Nat.pow a m) (Nat.pow a k)))
    (Nat.mul_one (Nat.pow a m)).symm
    (fun k ih => (congrArg (fun x => Nat.mul x a) ih).trans (Nat.mul_assoc (Nat.pow a m) (Nat.pow a k) a)) n

protected theorem pow_add' (a m n : Nat) :
    Eq (Nat.pow a (Nat.add m n)) (Nat.mul (Nat.pow a n) (Nat.pow a m)) :=
  (Nat.pow_add a m n).trans (Nat.mul_comm (Nat.pow a m) (Nat.pow a n))

protected theorem pow_mul (a m n : Nat) :
    Eq (Nat.pow a (Nat.mul m n)) (Nat.pow (Nat.pow a m) n) :=
  Nat.rec (motive := fun k => Eq (Nat.pow a (Nat.mul m k)) (Nat.pow (Nat.pow a m) k))
    Omega.rfl (fun k ih => (Nat.pow_add a (Nat.mul m k) m).trans (congrArg (fun x => Nat.mul x (Nat.pow a m)) ih)) n

protected theorem pow_mul' (a m n : Nat) :
    Eq (Nat.pow a (Nat.mul m n)) (Nat.pow (Nat.pow a n) m) :=
  (congrArg (Nat.pow a) (Nat.mul_comm m n)).trans (Nat.pow_mul a n m)

protected theorem pow_right_comm (a m n : Nat) :
    Eq (Nat.pow (Nat.pow a m) n) (Nat.pow (Nat.pow a n) m) :=
  (Nat.pow_mul a m n).symm.trans (Nat.pow_mul' a m n)

theorem two_pow_succ (n : Nat) :
    Eq (Nat.pow zero.succ.succ (Nat.add n zero.succ)) (Nat.add (Nat.pow zero.succ.succ n) (Nat.pow zero.succ.succ n)) :=
  Nat.mul_two (Nat.pow zero.succ.succ n)

end Omega.Nat

public section
namespace Nat
export _root_.Omega.Nat (add_add_add_comm add_eq_left add_eq_right add_eq_zero_iff add_left_cancel_iff add_left_inj add_right_cancel_iff add_right_inj add_sub_cancel_right add_succ_sub_one eq_zero_of_add_eq_zero_right left_eq_add lt_iff_add_one_le lt_one_add_iff mul_eq_zero mul_right_comm one_add one_add_le_iff one_add_sub_one one_le_of_lt one_lt_succ_succ one_pow pow_add pow_add' pow_add_one' pow_mul pow_mul' pow_right_comm pow_succ' pow_two pred_eq_of_eq_succ pred_one_add pred_sub right_eq_add sub_one sub_right_comm sub_succ' succ_add_eq_add_succ succ_add_sub_one succ_eq_one_add succ_le succ_ne_succ succ_sub_one two_pow_succ)
end Nat

namespace Omega.Nat
private theorem compareLog (k : Nat) :
    ∀ n, Not (Eq n 0) → Iff (Nat.le k (log2 n)) (Nat.le (Nat.pow 2 k) n) :=
  Nat.rec (motive := fun i => ∀ n, Not (Eq n 0) → Iff (Nat.le i (log2 n)) (Nat.le (Nat.pow 2 i) n))
    (fun n hn => Iff.intro (fun _ => Nat.pos_of_ne_zero hn) (fun _ => Nat.zero_le (log2 n)))
    (fun i ih n _ => Decidable.byCases (dec := Nat.decLe 2 n)
      (fun h =>
        let q := Nat.div n 2
        let qpos : Nat.lt 0 q := (Nat.le_div_iff_mul_le Nat.zero_lt_two).mpr h
        let logStep : Eq (log2 n) (Nat.succ (log2 q)) := (log2_def n).trans (ite_eq_left h)
        let decrease := ih q (Nat.ne_of_gt qpos)
        let lower : Iff (Nat.le i (log2 q)) (Nat.le (Nat.mul (Nat.pow 2 i) 2) n) :=
          decrease.trans (Nat.le_div_iff_mul_le Nat.zero_lt_two)
        Iff.intro
          (fun bound => lower.mp (Nat.le_of_succ_le_succ (Eq.subst (motive := Nat.le i.succ) logStep bound)))
          (fun bound => Eq.subst (motive := Nat.le i.succ) logStep.symm (Nat.succ_le_succ (lower.mpr bound))))
      (fun h =>
        let logZero : Eq (log2 n) 0 := (log2_def n).trans (ite_eq_right h)
        let twoBound : Nat.le 2 (Nat.pow 2 i.succ) := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.succ_le_succ (Nat.zero_le i))
        Iff.intro
          (fun bound => False.elim (Nat.not_succ_le_zero i (Eq.subst (motive := Nat.le i.succ) logZero bound)))
          (fun bound => False.elim (h (Nat.le_trans twoBound bound))))) k

private theorem leLog {n k : Nat} (h : Not (Eq n 0)) : Iff (Nat.le k (log2 n)) (Nat.le (Nat.pow 2 k) n) := compareLog k n h

private theorem logLt {n k : Nat} (h : Not (Eq n 0)) : Iff (Nat.lt (log2 n) k) (Nat.lt n (Nat.pow 2 k)) :=
  let projected := compareLog k n h
  Iff.intro
    (fun hl => Nat.not_le.mp (fun hp => Nat.not_le_of_lt hl (projected.mpr hp)))
    (fun hp => Nat.not_le.mp (fun hl => Nat.not_le_of_lt hp (projected.mp hl)))

private theorem logEq {n k : Nat} (h : Not (Eq n 0)) :
    Iff (Eq (log2 n) k) (And (Nat.le (Nat.pow 2 k) n) (Nat.lt n (Nat.pow 2 (Nat.succ k)))) :=
  Iff.intro
    (fun eq => ⟨(compareLog k n h).mp (Nat.le_of_eq eq.symm),
      (logLt h).mp (Eq.subst (motive := fun z => Nat.lt z k.succ) eq.symm (Nat.lt_succ_self _))⟩)
    (fun bounds => Nat.le_antisymm (Nat.le_of_lt_succ ((logLt h).mpr bounds.right))
      ((compareLog k n h).mpr bounds.left))

end Omega.Nat
port_proof Nat.le_log2 using Omega.Nat.leLog
port_proof Nat.log2_lt using Omega.Nat.logLt
port_proof Nat.log2_eq_iff using Omega.Nat.logEq

namespace Nat
export _root_.Omega.Nat (le_log2 log2_eq_iff log2_lt)
end Nat

port_private_declaration Nat.lt_of_add_lt_add_right.match_1_1
port_definition Nat.lt_of_add_lt_add_right._f
port_proof Nat.lt_of_add_lt_add_right by_constructive_casts
port_proof Nat.lt_of_add_lt_add_left by_constructive_casts
port_proof Nat.add_lt_add_iff_left by_constructive_casts
port_proof Nat.add_lt_add_iff_right by_constructive_casts
port_proof Nat.add_lt_add_of_le_of_lt by_constructive_casts
port_proof Nat.add_lt_add_of_lt_of_le by_constructive_casts
port_proof Nat.mod_add_mod by_constructive_casts
port_proof Nat.add_mod_mod by_constructive_casts
port_proof Nat.add_mod by_constructive_casts
port_proof Nat.add_mod_eq_add_mod_right by_constructive_casts
port_proof Nat.add_mod_eq_add_mod_left by_constructive_casts
port_proof Nat.add_one_mul_add_one by_constructive_casts
port_proof Nat.add_pos_left by_constructive_casts
port_private_declaration Nat.add_self_ne_one.match_1_1
port_proof Nat.add_self_ne_one by_constructive_casts
port_proof Nat.add_sub_cancel' by_constructive_casts
port_proof Nat.le_mul_of_pos_right by_constructive_casts
port_proof Nat.add_sub_one_le_mul by_constructive_casts
port_proof Nat.add_sub_sub_add_right by_constructive_casts
port_proof Nat.div_add_mod' by_constructive_casts
port_alternative_proof Nat.div_lt_one_iff from OmegaChecks.InitPort.Alternatives.NatOrder
namespace Omega.Nat
protected theorem div_eq_zero_iff {a b : Nat} :
    Iff (Eq (Nat.div a b) 0) (Or (Eq b 0) (Nat.lt a b)) :=
  Iff.intro (fun eq => (eq_zero_or_pos b).elim Or.inl (fun pos =>
    Or.inr ((div_lt_one_iff pos).mp (Eq.subst (motive := fun k => Nat.lt k 1) eq.symm Nat.zero_lt_one))))
    (fun h => h.elim (fun z => z.symm ▸ Nat.div_zero a) (fun lt => Nat.div_eq_of_lt lt))
end Omega.Nat
namespace Omega.Nat
protected theorem div_le_div_right {a b c : Nat} (h : Nat.le a b) :
    Nat.le (Nat.div a c) (Nat.div b c) :=
  Nat.rec (motive := fun k => Nat.le (Nat.div a k) (Nat.div b k))
    ((Nat.div_zero a).symm ▸ (Nat.div_zero b).symm ▸ Nat.le_refl 0)
    (fun k _ => (le_div_iff_mul_le (Nat.zero_lt_succ k)).2 (Nat.le_trans (div_mul_le_self ..) h)) c
end Omega.Nat
port_proof Nat.div_le_iff_le_mul_add_pred by_constructive_casts
port_proof Nat.div_mul_div_comm by_constructive_casts
port_proof Nat.mul_mul_mul_comm by_constructive_casts
port_alternative_proof Nat.div_mul_div_le from OmegaChecks.InitPort.Alternatives.NatOrder
namespace Omega.Nat
protected theorem div_ne_zero_iff {a b : Nat} :
    Iff (Ne (Nat.div a b) 0) (And (Ne b 0) (Nat.le b a)) :=
  Iff.intro (fun nz => And.intro (fun z => nz (Nat.div_eq_zero_iff.mpr (Or.inl z)))
    (Nat.le_of_not_gt (fun lt => nz (Nat.div_eq_zero_iff.mpr (Or.inr lt)))))
    (fun h z => (Nat.div_eq_zero_iff.mp z).elim h.left (Nat.not_lt_of_ge h.right))
end Omega.Nat
port_proof Nat.eq_div_of_mul_eq_left by_constructive_casts
port_proof Nat.eq_div_of_mul_eq_right by_constructive_casts
port_alternative_proof Nat.eq_of_dvd_of_lt_two_mul from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.exists_eq_add_of_le by_constructive_casts
port_proof Nat.exists_eq_add_of_le' by_constructive_casts
port_proof Nat.exists_eq_add_of_lt by_constructive_casts
port_alternative_proof Nat.exists_ne_zero from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.le_mul_of_pos_left by_constructive_casts
port_private_declaration Nat.le_mul_self.match_1_1
port_proof Nat.le_mul_self by_constructive_casts
port_proof Nat.le_of_mod_lt by_constructive_casts
port_private_declaration Nat.le_of_pred_lt.match_1_1
port_proof Nat.le_of_pred_lt by_constructive_casts
port_proof Nat.one_le_iff_ne_zero by_constructive_casts
port_private_declaration Nat.le_self_pow.match_1_1
port_proof Nat.le_self_pow by_constructive_casts
port_proof Nat.le_sub_of_add_le' by_constructive_casts
port_proof Nat.log2_self_le by_constructive_casts
port_proof Nat.log2_zero by_constructive_casts
port_proof Nat.lt_div_mul_add by_constructive_casts
port_private_declaration Nat.lt_iff_le_pred.match_1_1
port_proof Nat.lt_iff_le_pred by_constructive_casts
port_private_declaration Nat.lt_log2_self.match_1_1
port_proof Nat.lt_log2_self by_constructive_casts
port_proof Nat.lt_mul_div_succ by_constructive_casts
port_proof Nat.lt_mul_of_div_lt by_constructive_casts
port_proof Nat.lt_of_div_lt_div by_constructive_casts
port_proof Nat.mul_lt_mul_of_le_of_lt by_constructive_casts
port_proof Nat.pow_lt_pow_succ by_constructive_casts
port_proof Nat.lt_pow_self by_constructive_casts
port_proof Nat.lt_two_pow_self by_constructive_casts
port_proof Nat.mod_add_div' by_constructive_casts
port_proof Nat.mod_div_self by_constructive_casts
port_proof Nat.mod_eq_iff_lt by_constructive_casts
port_proof Nat.mod_eq_sub by_constructive_casts
port_proof Nat.mod_succ by_constructive_casts
port_proof Nat.mod_succ_eq_iff_lt by_constructive_casts
port_alternative_proof Nat.mod_two_eq_zero_or_one from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.mod_two_bne_zero from OmegaChecks.InitPort.Alternatives.NatBits
port_alternative_proof Nat.mod_two_not_eq_one from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.mod_two_ne_one by_constructive_casts
port_alternative_proof Nat.mod_two_not_eq_zero from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.mod_two_ne_zero by_constructive_casts
port_proof Nat.mod_two_pow_self by_constructive_casts
port_alternative_proof Nat.mul_add_div from OmegaChecks.InitPort.Alternatives.NatOrder
namespace Omega.Nat
theorem mul_div_le_mul_div_assoc (a b c : Nat) :
    Nat.le (Nat.mul a (Nat.div b c)) (Nat.div (Nat.mul a b) c) :=
  Nat.rec (motive := fun k => Nat.le (Nat.mul a (Nat.div b k)) (Nat.div (Nat.mul a b) k))
    ((Nat.div_zero b).symm ▸ (Nat.div_zero (Nat.mul a b)).symm ▸ Nat.le_refl 0)
    (fun k _ => (le_div_iff_mul_le (Nat.zero_lt_succ k)).2
      ((Nat.mul_assoc a (Nat.div b (succ k)) (succ k)).symm ▸
        Nat.mul_le_mul_left a (div_mul_le_self ..))) c
end Omega.Nat
port_proof Nat.mul_div_mul_comm by_constructive_casts
port_private_declaration Nat.mul_left_cancel.match_1_1
port_proof Nat.mul_left_cancel by_constructive_casts
port_private_declaration Nat.mul_left_cancel_iff.match_1_1
port_proof Nat.mul_left_cancel_iff by_constructive_casts
port_proof Nat.mul_right_inj by_constructive_casts
port_proof Nat.mul_eq_left by_constructive_casts
port_proof Nat.mul_right_cancel by_constructive_casts
port_private_declaration Nat.mul_right_cancel_iff.match_1_1
port_proof Nat.mul_right_cancel_iff by_constructive_casts
port_proof Nat.mul_left_inj by_constructive_casts
port_proof Nat.mul_eq_right by_constructive_casts
port_private_declaration Nat.mul_le_add_right.match_1_1
port_proof Nat.mul_le_add_right by_constructive_casts
port_proof Nat.mul_le_of_le_div by_constructive_casts
port_proof Nat.mul_lt_mul_of_le_of_lt' by_constructive_casts
port_proof Nat.mul_lt_mul_of_lt_of_le by_constructive_casts
port_proof Nat.mul_lt_mul_of_lt_of_le' by_constructive_casts
port_proof Nat.mul_mod by_constructive_casts
port_proof Nat.mul_mod_mul_right by_constructive_casts
port_proof Nat.mul_ne_mul_left by_constructive_casts
port_proof Nat.mul_ne_mul_right by_constructive_casts
port_proof Nat.mul_self_le_mul_self by_constructive_casts
port_proof Nat.mul_self_sub_mul_self_eq by_constructive_casts
port_proof Nat.not_dvd_of_pos_of_lt by_constructive_casts
port_proof Nat.not_succ_lt_self by_constructive_casts
port_proof Nat.one_le_div_iff by_constructive_casts
port_private_declaration Nat.one_lt_two_pow.match_1_1
port_proof Nat.one_lt_two_pow by_constructive_casts
namespace Omega.Nat
protected theorem one_le_two_pow {n : Nat} : Nat.le 1 (Nat.pow 2 n) :=
  Nat.two_pow_pos n
end Omega.Nat
port_proof Nat.one_lt_pow by_constructive_casts
port_proof Nat.one_lt_two_pow' by_constructive_casts
port_proof Nat.one_lt_two_pow_iff by_constructive_casts
port_proof Nat.one_mod by_constructive_casts
port_alternative_proof Nat.one_mod_eq_one from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.one_mod_two_pow_eq_one from OmegaChecks.InitPort.Alternatives.Word.BitVec
port_proof Nat.one_mod_two_pow by_constructive_casts
port_private_declaration Nat.one_sub.match_1_1
port_proof Nat.one_sub by_constructive_casts
port_proof Nat.pos_of_lt_add_right by_constructive_casts
port_proof Nat.pos_of_lt_add_left by_constructive_casts
port_proof Nat.pow_eq by_constructive_casts
port_proof Nat.pow_lt_pow_of_lt by_constructive_casts
port_proof Nat.pow_pred_mul by_constructive_casts
port_proof Nat.pow_sub_mul_pow by_constructive_casts
port_proof Nat.pow_two_sub_pow_two by_constructive_casts
port_private_declaration Nat.self_add_sub_one.match_1_1
port_proof Nat.self_add_sub_one by_constructive_casts
port_proof Nat.sub_one_add_self by_constructive_casts
port_proof Nat.pred_add_self by_constructive_casts
port_alternative_proof Nat.pred_eq_self_iff from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.self_add_pred by_constructive_casts
port_proof Nat.sub_add_comm by_constructive_casts
port_proof Nat.sub_lt_of_pos_le by_constructive_casts
port_proof Nat.sub_add_lt_sub by_constructive_casts
port_proof Nat.sub_lt_add_one by_constructive_casts
port_proof Nat.sub_lt_succ by_constructive_casts
port_proof Nat.sub_mod_eq_zero_of_mod_eq by_constructive_casts
port_proof Nat.sub_mul_div by_constructive_casts
port_private_declaration Nat.sub_mul_mod.match_1_1
port_definition Nat.sub_mul_mod._f
port_proof Nat.sub_mul_mod by_constructive_casts
port_proof Nat.sub_sub_self by_constructive_casts
port_proof Nat.succ_mul_pos by_constructive_casts
port_proof Nat.succ_mul_succ by_constructive_casts
port_proof Nat.succ_mul_succ_eq by_constructive_casts
port_proof Nat.succ_sub_sub_succ by_constructive_casts
port_proof Nat.two_pow_pred_mul_two by_constructive_casts
port_alternative_proof Nat.two_pow_pred_add_two_pow_pred from OmegaChecks.InitPort.Alternatives.Word.BitVec
port_proof Nat.two_pow_sub_two_pow_pred by_constructive_casts
port_proof Nat.zero_eq_mul by_constructive_casts

namespace Nat
export _root_.Omega.Nat (add_lt_add_iff_left add_lt_add_iff_right add_lt_add_of_le_of_lt
  add_lt_add_of_lt_of_le add_mod add_mod_eq_add_mod_left add_mod_eq_add_mod_right add_mod_mod
  add_one_mul_add_one add_pos_left add_self_ne_one add_sub_cancel' add_sub_one_le_mul
  add_sub_sub_add_right div_add_mod' div_eq_zero_iff div_le_div_right div_le_iff_le_mul_add_pred
  div_lt_one_iff div_mul_div_comm div_mul_div_le div_ne_zero_iff eq_div_of_mul_eq_left
  eq_div_of_mul_eq_right eq_of_dvd_of_lt_two_mul exists_eq_add_of_le exists_eq_add_of_le'
  exists_eq_add_of_lt exists_ne_zero le_mul_of_pos_left le_mul_of_pos_right le_mul_self le_of_mod_lt
  le_of_pred_lt le_self_pow le_sub_of_add_le' log2_self_le log2_zero lt_div_mul_add lt_iff_le_pred
  lt_log2_self lt_mul_div_succ lt_mul_of_div_lt lt_of_add_lt_add_left lt_of_add_lt_add_right
  lt_of_div_lt_div lt_pow_self lt_two_pow_self mod_add_div' mod_add_mod mod_div_self mod_eq_iff_lt
  mod_eq_sub mod_succ mod_succ_eq_iff_lt mod_two_bne_zero mod_two_eq_zero_or_one mod_two_ne_one
  mod_two_ne_zero mod_two_not_eq_one mod_two_not_eq_zero mod_two_pow_self mul_add_div
  mul_div_le_mul_div_assoc mul_div_mul_comm mul_eq_left mul_eq_right mul_le_add_right mul_le_of_le_div
  mul_left_cancel mul_left_cancel_iff mul_left_inj mul_lt_mul_of_le_of_lt mul_lt_mul_of_le_of_lt'
  mul_lt_mul_of_lt_of_le mul_lt_mul_of_lt_of_le' mul_mod mul_mod_mul_right mul_mul_mul_comm
  mul_ne_mul_left mul_ne_mul_right mul_right_cancel mul_right_cancel_iff mul_right_inj
  mul_self_le_mul_self mul_self_sub_mul_self_eq not_dvd_of_pos_of_lt not_succ_lt_self one_le_div_iff
  one_le_iff_ne_zero one_le_two_pow one_lt_pow one_lt_two_pow one_lt_two_pow' one_lt_two_pow_iff
  one_mod one_mod_eq_one one_mod_two_pow one_mod_two_pow_eq_one one_sub pos_of_lt_add_left
  pos_of_lt_add_right pow_eq pow_lt_pow_of_lt pow_lt_pow_succ pow_pred_mul pow_sub_mul_pow
  pow_two_sub_pow_two pred_add_self pred_eq_self_iff self_add_pred self_add_sub_one sub_add_comm
  sub_add_lt_sub sub_lt_add_one sub_lt_of_pos_le sub_lt_succ sub_mod_eq_zero_of_mod_eq sub_mul_div
  sub_mul_mod sub_one_add_self sub_sub_self succ_mul_pos succ_mul_succ succ_mul_succ_eq
  succ_sub_sub_succ two_pow_pred_add_two_pow_pred two_pow_pred_mul_two two_pow_sub_two_pow_pred
  zero_eq_mul)
end Nat

port_proof Nat.add_left_max_self by_constructive_casts
port_proof Nat.add_left_min_self by_constructive_casts
port_proof Nat.add_right_max_self by_constructive_casts
port_proof Nat.add_right_min_self by_constructive_casts
port_definition Nat.decidableBallLT.match_1
port_definition Nat.decidableBallLT.match_3
port_definition Nat.decidableBallLT.match_5
port_definition Nat.decidableExistsFin.match_1
port_definition Nat.decidableExistsFin.match_3
port_definition Nat.decidableExistsLT'.match_1
port_definition Nat.decidableExistsLT.match_1
port_definition Nat.decidableForallFin.match_1
port_private_declaration Nat.div_div_div_eq_div.match_1_1
port_proof Nat.div_div_div_eq_div by_constructive_casts
port_proof Nat.div_dvd_div by_constructive_casts
port_private_declaration Nat.mul_dvd_mul_iff_left.match_1_1
port_proof Nat.mul_dvd_mul_iff_left by_constructive_casts
port_proof Nat.div_dvd_iff_dvd_mul by_constructive_casts
port_proof Nat.div_dvd_of_dvd by_constructive_casts
port_proof Nat.eq_mul_of_div_eq_right by_constructive_casts
port_proof Nat.eq_mul_of_div_eq_left by_constructive_casts
port_proof Nat.div_eq_iff_eq_of_dvd_dvd by_constructive_casts
port_proof Nat.div_left_inj by_constructive_casts
port_proof Nat.lt_div_iff_mul_lt' by_constructive_casts
port_proof Nat.div_lt_div_of_lt_of_dvd by_constructive_casts
port_proof Nat.div_lt_div_right by_constructive_casts
port_private_declaration Nat.div_mod_unique.match_1_1
port_private_declaration Nat.div_mod_unique.match_1_3
port_proof Nat.div_mod_unique by_constructive_casts
port_proof Nat.div_mul_right_comm by_constructive_casts
port_alternative_proof Nat.le_iff_ne_zero_of_dvd from OmegaChecks.InitPort.Alternatives.NatOrder
namespace Omega.Nat
public theorem div_ne_zero_iff_of_dvd {b a : Nat} (hba : @Omega.Dvd.dvd Nat Omega.Nat.instDvd b a) :
    Iff (Ne (Nat.div a b) Nat.zero) (And (Ne a Nat.zero) (Ne b Nat.zero)) :=
  Iff.intro (fun nz =>
    let h := Nat.div_ne_zero_iff.mp nz
    And.intro ((Nat.le_iff_ne_zero_of_dvd h.left hba).mp h.right) h.left)
    (fun h => Nat.div_ne_zero_iff.mpr (And.intro h.right ((Nat.le_iff_ne_zero_of_dvd h.right hba).mpr h.left)))
end Omega.Nat
port_proof Nat.div_pos_iff by_constructive_casts
port_proof Nat.dvd_add_left by_constructive_casts
port_proof Nat.dvd_add_right by_constructive_casts
port_proof Nat.dvd_iff_div_mul_eq by_constructive_casts
port_proof Nat.dvd_iff_dvd_dvd by_constructive_casts
port_proof Nat.dvd_mul_of_div_dvd by_constructive_casts
port_proof Nat.pow_dvd_pow by_constructive_casts
port_proof Nat.pow_dvd_of_le_of_pow_dvd by_constructive_casts
port_proof Nat.dvd_of_pow_dvd by_constructive_casts
port_proof Nat.eq_of_dvd_of_div_eq_one by_constructive_casts
port_proof Nat.eq_one_of_mul_eq_one_right by_constructive_casts
port_proof Nat.eq_one_of_mul_eq_one_left by_constructive_casts
port_proof Nat.eq_zero_of_dvd_of_div_eq_zero by_constructive_casts
port_alternative_proof Nat.eq_zero_of_dvd_of_lt from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.succ_max_succ by_constructive_casts
port_private_declaration Nat.max_assoc.match_1_1
port_definition Nat.max_assoc._f by_constructive_casts
port_proof Nat.max_assoc by_constructive_casts
port_proof Nat.instAssociativeMax by_constructive_casts
port_alternative_proof Nat.min_assoc from OmegaChecks.InitPort.Alternatives.Extract
port_proof Nat.instAssociativeMin by_constructive_casts
public protected theorem Omega.Nat.max_self (a : Nat) : Eq (Nat.max a a) a :=
  Omega.Nat.max_eq_right (Omega.Nat.le_refl a)
port_proof Nat.instIdempotentOpMax by_constructive_casts
public protected theorem Omega.Nat.min_self (a : Nat) : Eq (Nat.min a a) a :=
  Omega.Nat.min_eq_left (Omega.Nat.le_refl a)
port_proof Nat.instIdempotentOpMin by_constructive_casts
port_proof Nat.instLawfulIdentityMaxOfNat by_constructive_casts
port_proof Nat.le_of_lt_add_of_dvd by_constructive_casts
port_proof Nat.mul_ne_zero_iff by_constructive_casts
port_proof Nat.mul_ne_zero by_constructive_casts
port_proof Nat.log2_two_mul by_constructive_casts
port_alternative_proof Nat.lt_div_iff_mul_lt_of_dvd from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.lt_mul_iff_one_lt_left by_constructive_casts
port_proof Nat.lt_mul_iff_one_lt_right by_constructive_casts
port_private_declaration Nat.lt_mul_self_iff.match_1_1
port_proof Nat.lt_mul_self_iff by_constructive_casts
port_proof Nat.max_add_left_self by_constructive_casts
port_proof Nat.max_add_right_self by_constructive_casts
port_proof Nat.max_left_comm by_constructive_casts
port_proof Nat.succ_min_succ by_constructive_casts
port_private_declaration Nat.max_min_distrib_left.match_1_1
port_definition Nat.max_min_distrib_left._f by_constructive_casts
port_proof Nat.max_min_distrib_left by_constructive_casts
port_proof Nat.max_min_distrib_right by_constructive_casts
port_proof Nat.max_right_comm by_constructive_casts
port_proof Nat.min_add_left_self by_constructive_casts
port_proof Nat.min_add_right_self by_constructive_casts
port_alternative_proof Nat.min_eq_zero_iff from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.min_left_comm by_constructive_casts
port_private_declaration Nat.min_max_distrib_left.match_1_1
port_definition Nat.min_max_distrib_left._f by_constructive_casts
port_proof Nat.min_max_distrib_left by_constructive_casts
port_proof Nat.min_max_distrib_right by_constructive_casts
port_proof Nat.min_right_comm by_constructive_casts
port_proof Nat.min_self_assoc by_constructive_casts
port_proof Nat.min_self_assoc' by_constructive_casts
port_proof Nat.mod_mod by_constructive_casts
port_proof Nat.mul_mod_mod by_constructive_casts
port_proof Nat.mod_mul_mod by_constructive_casts
port_proof Nat.mul_div_cancel_left' by_constructive_casts
port_proof Nat.mul_div_eq_iff_dvd by_constructive_casts
port_proof Nat.mul_div_right_comm by_constructive_casts
port_proof Nat.mul_dvd_mul_iff_right by_constructive_casts
port_private_declaration Nat.mul_dvd_of_dvd_div.match_1_1
port_proof Nat.mul_dvd_of_dvd_div by_constructive_casts
port_proof Nat.mul_lt_mul_pow_succ by_constructive_casts
port_proof Nat.ne_zero_of_mul_ne_zero_left by_constructive_casts
port_proof Nat.ne_zero_of_mul_ne_zero_right by_constructive_casts
port_proof Nat.one_shiftLeft by_constructive_casts
port_proof Nat.pow_mod by_constructive_casts
port_private_declaration Nat.pred_max_pred.match_1_1
port_proof Nat.pred_max_pred by_constructive_casts
port_private_declaration Nat.pred_min_pred.match_1_1
port_proof Nat.pred_min_pred by_constructive_casts
port_proof Nat.shiftLeft_succ_inside by_constructive_casts
port_private_declaration Nat.shiftLeft_succ.match_1_1
port_definition Nat.shiftLeft_succ._f by_constructive_casts
port_proof Nat.shiftLeft_succ by_constructive_casts
port_private_declaration Nat.shiftLeft_add._simp_1_3
port_private_declaration Nat.shiftLeft_add.match_1_1
port_definition Nat.shiftLeft_add._f by_constructive_casts
port_proof Nat.shiftLeft_add by_constructive_casts
port_proof Nat.shiftLeft_shiftRight by_constructive_casts
port_proof Nat.shiftLeft_zero by_constructive_casts
port_private_declaration Nat.shiftRight_succ_inside.match_1_1
port_definition Nat.shiftRight_succ_inside._f by_constructive_casts
port_proof Nat.shiftRight_succ_inside by_constructive_casts
port_proof Nat.sub_eq_sub_min by_constructive_casts
port_proof Nat.sub_add_min_cancel by_constructive_casts
port_proof Nat.sub_eq_max_sub by_constructive_casts
port_definition Nat.sub_lt_self
port_private_declaration Nat.sub_max_sub_right.match_1_1
port_definition Nat.sub_max_sub_right._f by_constructive_casts
port_proof Nat.sub_max_sub_right by_constructive_casts
port_alternative_proof Nat.sub_min_sub_right from OmegaChecks.InitPort.Alternatives.Extract
port_private_declaration Nat.sub_sub_eq_min.match_1_1
port_definition Nat.sub_sub_eq_min._f by_constructive_casts
port_proof Nat.sub_sub_eq_min by_constructive_casts
port_private_declaration Nat.zero_shiftLeft.match_1_1
port_definition Nat.zero_shiftLeft._f by_constructive_casts
port_proof Nat.zero_shiftLeft by_constructive_casts
port_private_declaration Nat.zero_shiftRight.match_1_1
port_definition Nat.zero_shiftRight._f by_constructive_casts
port_proof Nat.zero_shiftRight by_constructive_casts

namespace Nat
export _root_.Omega.Nat (add_left_max_self add_left_min_self add_right_max_self add_right_min_self
  div_div_div_eq_div div_dvd_div div_dvd_iff_dvd_mul div_dvd_of_dvd div_eq_iff_eq_of_dvd_dvd
  div_left_inj div_lt_div_of_lt_of_dvd div_lt_div_right div_mod_unique div_mul_right_comm
  div_ne_zero_iff_of_dvd div_pos_iff dvd_add_left dvd_add_right dvd_iff_div_mul_eq dvd_iff_dvd_dvd
  dvd_mul_of_div_dvd dvd_of_pow_dvd eq_mul_of_div_eq_left eq_mul_of_div_eq_right
  eq_of_dvd_of_div_eq_one eq_one_of_mul_eq_one_left eq_one_of_mul_eq_one_right
  eq_zero_of_dvd_of_div_eq_zero eq_zero_of_dvd_of_lt instAssociativeMax instAssociativeMin
  instIdempotentOpMax instIdempotentOpMin instLawfulIdentityMaxOfNat le_iff_ne_zero_of_dvd
  le_of_lt_add_of_dvd log2_two_mul lt_div_iff_mul_lt' lt_div_iff_mul_lt_of_dvd lt_mul_iff_one_lt_left
  lt_mul_iff_one_lt_right lt_mul_self_iff max_add_left_self max_add_right_self max_assoc max_left_comm
  max_min_distrib_left max_min_distrib_right max_right_comm max_self min_add_left_self
  min_add_right_self min_assoc min_eq_zero_iff min_left_comm min_max_distrib_left
  min_max_distrib_right min_right_comm min_self min_self_assoc min_self_assoc' mod_mod mod_mul_mod
  mul_div_cancel_left' mul_div_eq_iff_dvd mul_div_right_comm mul_dvd_mul_iff_left
  mul_dvd_mul_iff_right mul_dvd_of_dvd_div mul_lt_mul_pow_succ mul_mod_mod mul_ne_zero mul_ne_zero_iff
  ne_zero_of_mul_ne_zero_left ne_zero_of_mul_ne_zero_right one_shiftLeft pow_dvd_of_le_of_pow_dvd
  pow_dvd_pow pow_mod pred_max_pred pred_min_pred shiftLeft_add shiftLeft_shiftRight shiftLeft_succ
  shiftLeft_succ_inside shiftLeft_zero shiftRight_succ_inside sub_add_min_cancel sub_eq_max_sub
  sub_eq_sub_min sub_lt_self sub_max_sub_right sub_min_sub_right sub_sub_eq_min succ_max_succ
  succ_min_succ zero_shiftLeft zero_shiftRight)
end Nat

port_proof Nat.add_le_of_le_sub' by_constructive_casts
port_proof Nat.add_lt_of_lt_sub' by_constructive_casts
port_proof Nat.decidableBallLE._proof_1 by_constructive_casts
port_proof Nat.decidableBallLT._proof_7 by_constructive_casts
port_proof Nat.decidableBallLT._proof_8 by_constructive_casts
port_definition Nat.decidableBallLT._f by_constructive_casts
port_definition Nat.decidableBallLT by_constructive_casts
port_definition Nat.decidableBallLE by_constructive_casts
port_proof Nat.div_div_self by_constructive_casts
port_proof Nat.div_eq_iff_eq_mul_right by_constructive_casts
port_proof Nat.div_eq_iff_eq_mul_left by_constructive_casts
port_proof Nat.div_eq_sub_mod_div by_constructive_casts
port_proof Nat.div_le_div_of_mul_le_mul by_constructive_casts
port_proof Nat.div_le_iff_le_mul_of_dvd by_constructive_casts
port_proof Nat.div_mul_div_le_div by_constructive_casts
port_private_declaration Nat.dvd_div_of_mul_dvd.match_1_1
port_proof Nat.dvd_div_of_mul_dvd by_constructive_casts
port_proof Nat.dvd_div_iff_mul_dvd by_constructive_casts
port_proof Nat.dvd_iff_le_div_mul by_constructive_casts
port_proof Nat.dvd_sub_mod by_constructive_casts
port_proof Nat.eq_div_iff_mul_eq_left by_constructive_casts
port_private_declaration Nat.le_of_sub_le_sub_left.match_1_1
port_definition Nat.le_of_sub_le_sub_left._f by_constructive_casts
port_proof Nat.le_of_sub_le_sub_left by_constructive_casts
port_proof Nat.le_succ_iff by_constructive_casts
port_proof Nat.le_one_iff_eq_zero_or_eq_one by_constructive_casts
port_proof Nat.le_sub_iff_add_le by_constructive_casts
port_proof Nat.le_sub_iff_add_le' by_constructive_casts
port_proof Nat.lt_add_left_iff_pos by_constructive_casts
port_proof Nat.lt_add_right_iff_pos by_constructive_casts
port_proof Nat.lt_sub_iff_add_lt by_constructive_casts
port_alternative_proof Nat.lt_sub_iff_add_lt' from OmegaChecks.InitPort.Alternatives.NatOrder
port_private_declaration Nat.mul_add_mod.match_1_1
port_definition Nat.mul_add_mod._f by_constructive_casts
port_proof Nat.mul_add_mod by_constructive_casts
port_proof Nat.mod_eq_iff by_constructive_casts
port_proof Nat.mul_add_mod' by_constructive_casts
port_proof Nat.mul_add_mod_of_lt by_constructive_casts
port_proof Nat.mul_add_mul_div_of_dvd by_constructive_casts
port_proof Nat.mul_lt_mul_of_lt_of_lt by_constructive_casts
port_private_declaration Nat.mul_sub_div_of_dvd._simp_1_1
port_proof Nat.mul_sub_div_of_dvd by_constructive_casts
port_proof Nat.mul_sub_mul_div_of_dvd by_constructive_casts
port_proof Nat.one_le_pow by_constructive_casts
port_proof Nat.one_lt_pow' by_constructive_casts
port_alternative_proof Nat.pow_lt_pow_iff_left from OmegaChecks.InitPort.Alternatives.NatOrder
namespace Omega.Nat
public theorem one_lt_pow_iff {n : Nat} (hn : Ne n Nat.zero) : ∀ {a : Nat},
    Iff (Nat.lt (Nat.succ Nat.zero) (Nat.pow a n)) (Nat.lt (Nat.succ Nat.zero) a) :=
  fun {a} => Eq.subst (motive := fun k => Iff (Nat.lt k (Nat.pow a n)) (Nat.lt (Nat.succ Nat.zero) a))
    (Nat.one_pow n) (Nat.pow_lt_pow_iff_left (a := Nat.succ Nat.zero) (b := a) hn)
end Omega.Nat
port_proof Nat.pow_div by_constructive_casts
port_proof Nat.pow_le_one_iff by_constructive_casts
port_proof Nat.pow_le_pow_of_le by_constructive_casts
port_alternative_proof Nat.pow_pred_lt_pow from OmegaChecks.InitPort.Alternatives.Word.BitVec
port_proof Nat.pow_self_mul_pow_self_le by_constructive_casts
port_proof Nat.sub_eq_zero_iff_le by_constructive_casts
port_private_declaration Nat.sub_add_eq_max.match_1_1
port_proof Nat.sub_add_eq_max by_constructive_casts
port_proof Nat.sub_le_iff_le_add by_constructive_casts
port_proof Nat.sub_le_iff_le_add' by_constructive_casts
port_proof Nat.sub_le_sub_iff_left by_constructive_casts
port_proof Nat.sub_one_lt_of_le by_constructive_casts
port_proof Nat.sub_one_sub_lt by_constructive_casts
port_proof Nat.sub_pos_iff_lt by_constructive_casts
port_alternative_proof Nat.two_pow_pred_lt_two_pow from OmegaChecks.InitPort.Alternatives.Word.BitVec
port_alternative_proof Nat.two_pow_pred_mod_two_pow from OmegaChecks.InitPort.Alternatives.Word.BitVec

namespace Nat
export _root_.Omega.Nat (add_le_of_le_sub' add_lt_of_lt_sub' decidableBallLE decidableBallLT
  div_div_self div_eq_iff_eq_mul_left div_eq_iff_eq_mul_right div_eq_sub_mod_div
  div_le_div_of_mul_le_mul div_le_iff_le_mul_of_dvd div_mul_div_le_div dvd_div_iff_mul_dvd
  dvd_div_of_mul_dvd dvd_iff_le_div_mul dvd_sub_mod eq_div_iff_mul_eq_left le_of_sub_le_sub_left
  le_one_iff_eq_zero_or_eq_one le_sub_iff_add_le le_sub_iff_add_le' le_succ_iff lt_add_left_iff_pos
  lt_add_right_iff_pos lt_sub_iff_add_lt lt_sub_iff_add_lt' mod_eq_iff mul_add_mod mul_add_mod'
  mul_add_mod_of_lt mul_add_mul_div_of_dvd mul_lt_mul_of_lt_of_lt mul_sub_div_of_dvd
  mul_sub_mul_div_of_dvd one_le_pow one_lt_pow' one_lt_pow_iff pow_div pow_le_one_iff pow_le_pow_of_le
  pow_lt_pow_iff_left pow_pred_lt_pow pow_self_mul_pow_self_le sub_add_eq_max sub_eq_zero_iff_le
  sub_le_iff_le_add sub_le_iff_le_add' sub_le_sub_iff_left sub_one_lt_of_le sub_one_sub_lt
  sub_pos_iff_lt two_pow_pred_lt_two_pow two_pow_pred_mod_two_pow)
end Nat

port_proof Nat.decidableExistsFin._proof_1 by_constructive_casts
port_proof Nat.decidableExistsLT._proof_10 by_constructive_casts
port_proof Nat.decidableExistsLT._proof_5 by_constructive_casts
port_definition Nat.decidableExistsLT._f by_constructive_casts
port_definition Nat.decidableExistsLT by_constructive_casts
port_definition Nat.decidableExistsFin by_constructive_casts
port_proof Nat.decidableExistsLE._proof_1 by_constructive_casts
port_definition Nat.decidableExistsLE by_constructive_casts
port_proof Nat.decidableForallFin._proof_1 by_constructive_casts
port_definition Nat.decidableForallFin by_constructive_casts
attribute [instance] Omega.Nat.decidableBallLT Omega.Nat.decidableForallFin Omega.Nat.decidableBallLE
  Omega.Nat.decidableExistsLT Omega.Nat.decidableExistsLE Omega.Nat.decidableExistsFin
port_proof Nat.div_eq_self by_constructive_casts
port_private_declaration Nat.zero_pow.match_1_1
port_proof Nat.zero_pow by_constructive_casts
port_alternative_proof Nat.div_pow from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.div_pow_of_pos by_constructive_casts
port_alternative_proof Nat.pow_eq_zero from OmegaChecks.InitPort.Alternatives.NatOrder
namespace Omega.Nat
public protected theorem pow_lt_pow_iff_right {a n m : Nat} (h : Nat.lt (Nat.succ Nat.zero) a) :
    Iff (Nat.lt (Nat.pow a n) (Nat.pow a m)) (Nat.lt n m) :=
  Iff.intro (fun lt => Nat.lt_of_not_ge (fun rev => Nat.not_le_of_lt lt (Nat.pow_le_pow_of_le h rev)))
    (Nat.pow_lt_pow_of_lt h)
end Omega.Nat
namespace Omega.Nat
public theorem log2_two_pow {n : Nat} : Eq (Nat.log2 (Nat.pow (Nat.succ (Nat.succ Nat.zero)) n)) n :=
  (Nat.log2_eq_iff (Nat.ne_of_gt (Nat.pow_pos (Nat.succ_pos _)))).mpr
    (And.intro (Nat.le_refl _) (Nat.pow_lt_pow_of_lt Nat.one_lt_two (Nat.lt_succ_self n)))
end Omega.Nat
port_proof Nat.lt_of_pow_dvd_right by_constructive_casts
port_proof Nat.mul_div_lt_iff_not_dvd by_constructive_casts
port_proof Nat.pos_of_mul_pos_left by_constructive_casts
port_proof Nat.mul_pos_iff_of_pos_left by_constructive_casts
port_proof Nat.pos_of_mul_pos_right by_constructive_casts
port_proof Nat.mul_pos_iff_of_pos_right by_constructive_casts
port_alternative_proof Nat.mul_sub_mod from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.one_lt_mul_iff by_constructive_casts
namespace Omega.Nat
public protected theorem pow_le_pow_iff_right {a n m : Nat} (h : Nat.lt (Nat.succ Nat.zero) a) :
    Iff (Nat.le (Nat.pow a n) (Nat.pow a m)) (Nat.le n m) :=
  Iff.intro (fun le => Nat.le_of_not_gt (fun rev => Nat.not_lt_of_ge le (Nat.pow_lt_pow_of_lt h rev)))
    (Nat.pow_le_pow_of_le h)
end Omega.Nat
port_private_declaration Nat.pow_dvd_pow_iff_pow_le_pow.match_1_1
port_proof Nat.pow_dvd_pow_iff_pow_le_pow by_constructive_casts
port_proof Nat.pow_dvd_pow_iff_le_right by_constructive_casts
port_proof Nat.pow_dvd_pow_iff_le_right' by_constructive_casts
port_proof Nat.pow_eq_one by_constructive_casts
port_alternative_proof Nat.pow_right_inj from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.pow_eq_self_iff by_constructive_casts
port_proof Nat.pow_le_pow_iff_left by_constructive_casts
port_proof Nat.pow_lt_pow_right by_constructive_casts
namespace Omega.Nat
public protected theorem pow_pos_iff {a n : Nat} :
    Iff (Nat.lt Nat.zero (Nat.pow a n)) (Or (Nat.lt Nat.zero a) (Eq n Nat.zero)) :=
  Iff.intro (fun hp => (Nat.eq_zero_or_pos a).elim
    (fun az => Or.inr ((Nat.eq_zero_or_pos n).elim (fun nz => nz) (fun np => False.elim
      (Nat.ne_of_gt hp (Nat.pow_eq_zero.mpr (And.intro az (Nat.ne_of_gt np))))))) Or.inl)
    (fun h => h.elim Nat.pow_pos (fun nz => Eq.subst (motive := fun k => Nat.lt Nat.zero (Nat.pow a k))
      nz.symm Nat.zero_lt_one))
end Omega.Nat
port_proof Nat.pow_self_pos by_constructive_casts
port_private_declaration Nat.succ_mod_succ_eq_zero_iff._simp_1_4
port_proof Nat.succ_mod_succ_eq_zero_iff by_constructive_casts

namespace Nat
export _root_.Omega.Nat (decidableExistsFin decidableExistsLE decidableExistsLT decidableForallFin
  div_eq_self div_pow div_pow_of_pos log2_two_pow lt_of_pow_dvd_right mul_div_lt_iff_not_dvd
  mul_pos_iff_of_pos_left mul_pos_iff_of_pos_right mul_sub_mod one_lt_mul_iff pos_of_mul_pos_left
  pos_of_mul_pos_right pow_dvd_pow_iff_le_right pow_dvd_pow_iff_le_right' pow_dvd_pow_iff_pow_le_pow
  pow_eq_one pow_eq_self_iff pow_eq_zero pow_le_pow_iff_left pow_le_pow_iff_right pow_lt_pow_iff_right
  pow_lt_pow_right pow_pos_iff pow_right_inj pow_self_pos succ_mod_succ_eq_zero_iff zero_pow)
end Nat

port_alternative_proof Nat.add_eq_zero from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.le_iff_lt_add_one from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.le_add_one_iff from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.add_lt_iff_lt_sub_right from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.lt_of_lt_pred from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.sub_eq_of_eq_add' from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.eq_sub_of_add_eq from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.eq_sub_of_add_eq' from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.add_pos_iff_pos_or_pos from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.le_and_le_add_one_iff from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.le_add_pred_of_pos from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.mul_lt_mul'' from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.pos_of_lt_mul_left from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.pos_of_lt_mul_right from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.eq_zero_of_two_mul_le from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.add_succ_lt_add from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.sub_lt_iff_lt_add from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.sub_lt_iff_lt_add' from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.sub_min_sub_left from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.sub_max_sub_left from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.max_eq_zero_iff from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.lt_mul_div_self_add from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.exists_eq_add_one from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.exists_add_one_eq from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.pred_eq_succ_iff from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.add_eq_max_iff from OmegaChecks.InitPort.Alternatives.NatOrder
port_alternative_proof Nat.add_eq_min_iff from OmegaChecks.InitPort.Alternatives.NatOrder
port_proof Nat.mul_self_lt_mul_self by_constructive_casts
port_proof Nat.mul_self_le_mul_self_iff by_constructive_casts
port_proof Nat.mul_self_lt_mul_self_iff by_constructive_casts
port_proof Nat.eq_zero_of_mul_le by_constructive_casts
port_proof Nat.eq_zero_of_le_div by_constructive_casts
port_proof Nat.eq_zero_of_le_div_two by_constructive_casts
port_alternative_proof Nat.mul_self_inj from OmegaChecks.InitPort.Alternatives.NatOrder

namespace Nat
export _root_.Omega.Nat (add_eq_max_iff add_eq_min_iff add_eq_zero add_lt_iff_lt_sub_right
  add_pos_iff_pos_or_pos add_succ_lt_add eq_sub_of_add_eq eq_sub_of_add_eq' eq_zero_of_le_div
  eq_zero_of_le_div_two eq_zero_of_mul_le eq_zero_of_two_mul_le exists_add_one_eq exists_eq_add_one
  le_add_one_iff le_add_pred_of_pos le_and_le_add_one_iff le_iff_lt_add_one lt_mul_div_self_add
  lt_of_lt_pred max_eq_zero_iff mul_lt_mul'' mul_self_inj mul_self_le_mul_self_iff
  mul_self_lt_mul_self mul_self_lt_mul_self_iff pos_of_lt_mul_left pos_of_lt_mul_right
  pred_eq_succ_iff sub_eq_of_eq_add' sub_lt_iff_lt_add sub_lt_iff_lt_add' sub_max_sub_left
  sub_min_sub_left)
end Nat
