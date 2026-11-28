/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude

public import OmegaInit.Data.Nat.Basic

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
