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
