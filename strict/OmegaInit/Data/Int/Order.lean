/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaInit.Data.Int.Basic
import OmegaInit.Data.Int.Lemmas
import all OmegaInit.Data.Int.Basic
import all OmegaInit.Prelude

@[expose] public section

attribute [local semireducible] Omega.Nat.add Omega.Int.subNatNat

namespace Omega.Int

theorem nonneg_def {a : Int} : Iff (NonNeg a) (Exists (fun n : Nat => Eq a (ofNat n))) :=
  Iff.intro (NonNeg.rec (motive := fun a _ => Exists (fun n : Nat => Eq a (ofNat n)))
    (fun n => Exists.intro n rfl))
    (fun h => h.elim fun n e => Eq.subst (motive := NonNeg) e.symm (NonNeg.mk n))

theorem nonneg_or_nonneg_neg (a : Int) : Or (NonNeg a) (NonNeg a.neg) :=
  Int.rec (motive := fun a => Or (NonNeg a) (NonNeg a.neg))
    (fun n => Or.inl (NonNeg.mk n)) (fun n => Or.inr (NonNeg.mk n.succ)) a

theorem le_def {a b : Int} : Iff (a.le b) (NonNeg (b.sub a)) := Iff.intro (fun h => h) (fun h => h)

theorem le.intro_sub {a b : Int} (n : Nat) (h : Eq (b.sub a) (ofNat n)) : a.le b :=
  Eq.subst (motive := NonNeg) h.symm (NonNeg.mk n)

theorem le.intro {a b : Int} (n : Nat) (h : Eq (a.add (ofNat n)) b) : a.le b :=
  le.intro_sub n ((congrArg (fun x : Int => x.sub a) (h.symm.trans (Int.add_comm a (ofNat n)))).trans
    (Int.add_sub_cancel (ofNat n) a))

theorem le.dest_sub {a b : Int} (h : a.le b) : Exists (fun n : Nat => Eq (b.sub a) (ofNat n)) :=
  nonneg_def.mp h

theorem le.dest {a b : Int} (h : a.le b) : Exists (fun n : Nat => Eq (a.add (ofNat n)) b) :=
  (le.dest_sub h).elim fun n e => Exists.intro n ((congrArg a.add e.symm).trans
    ((Int.add_comm a (b.sub a)).trans (Int.sub_add_cancel b a)))

protected theorem le_refl (a : Int) : a.le a := le.intro Nat.zero (Int.add_zero a)

protected theorem le_rfl {a : Int} : a.le a := Int.le_refl a

protected theorem le_of_eq {a b : Int} (hab : Eq a b) : a.le b :=
  Eq.subst (motive := a.le) hab (Int.le_refl a)

protected theorem ge_of_eq {a b : Int} (hab : Eq a b) : b.le a := Int.le_of_eq hab.symm

protected theorem le_trans {a b c : Int} (h₁ : a.le b) (h₂ : b.le c) : a.le c :=
  (le.dest h₁).elim fun n hn => (le.dest h₂).elim fun m hm =>
    le.intro (n.add m) ((Int.add_assoc a (ofNat n) (ofNat m)).symm.trans
      ((congrArg (fun x : Int => x.add (ofNat m)) hn).trans hm))

protected theorem le_total (a b : Int) : Or (a.le b) (b.le a) :=
  (nonneg_or_nonneg_neg (b.sub a)).elim Or.inl
    (fun h => Or.inr (Eq.subst (motive := NonNeg) (Int.neg_sub b a) h))

protected theorem le_antisymm {a b : Int} (h₁ : a.le b) (h₂ : b.le a) : Eq a b :=
  (le.dest h₁).elim fun n hn => (le.dest h₂).elim fun m hm =>
    have cycle : Eq (a.add (ofNat (n.add m))) (a.add (ofNat Nat.zero)) :=
      (Int.add_assoc a (ofNat n) (ofNat m)).symm.trans
        ((congrArg (fun x : Int => x.add (ofNat m)) hn).trans (hm.trans (Int.add_zero a).symm))
    have hn0 := (Nat.eq_zero_of_add_eq_zero (Int.ofNat_inj.mp (Int.add_left_cancel cycle))).left
    (Int.add_zero a).symm.trans ((congrArg (fun n => a.add (ofNat n)) hn0.symm).trans hn)

protected theorem le_antisymm_iff {a b : Int} : Iff (Eq a b) (And (a.le b) (b.le a)) :=
  Iff.intro (fun h => And.intro (Int.le_of_eq h) (Int.ge_of_eq h))
    (fun both => Int.le_antisymm both.left both.right)

protected theorem add_le_add_left {a b : Int} (h : a.le b) (c : Int) : (c.add a).le (c.add b) :=
  (le.dest h).elim fun n e => le.intro n ((Int.add_assoc c a (ofNat n)).trans (congrArg c.add e))

protected theorem add_le_add_right {a b : Int} (h : a.le b) (c : Int) : (a.add c).le (b.add c) :=
  (le.dest h).elim fun n e => le.intro n ((Int.add_right_comm a c (ofNat n)).trans
    (congrArg (fun x : Int => x.add c) e))

protected theorem le_of_add_le_add_left {a b c : Int} (h : (a.add b).le (a.add c)) : b.le c :=
  (le.dest h).elim fun n e => le.intro n
    (Int.add_left_cancel ((Int.add_assoc a b (ofNat n)).symm.trans e))

protected theorem add_le_add {a b c d : Int} (h₁ : a.le b) (h₂ : c.le d) :
    (a.add c).le (b.add d) := Int.le_trans (Int.add_le_add_right h₁ c) (Int.add_le_add_left h₂ b)

protected theorem le_of_lt {a b : Int} (h : a.lt b) : a.le b :=
  Int.le_trans (le.intro Nat.zero.succ rfl) h

protected theorem lt_of_le_of_lt {a b c : Int} (h₁ : a.le b) (h₂ : b.lt c) : a.lt c :=
  Int.le_trans (Int.add_le_add_right h₁ (ofNat Nat.zero.succ)) h₂

protected theorem lt_of_lt_of_le {a b c : Int} (h₁ : a.lt b) (h₂ : b.le c) : a.lt c :=
  Int.le_trans h₁ h₂

protected theorem lt_trans {a b c : Int} (h₁ : a.lt b) (h₂ : b.lt c) : a.lt c :=
  Int.lt_of_lt_of_le h₁ (Int.le_of_lt h₂)

protected theorem lt_irrefl (a : Int) : Not (a.lt a) := fun h =>
  (le.dest h).elim fun n e =>
    have cycle : Eq (a.add (ofNat (Nat.zero.succ.add n))) (a.add (ofNat Nat.zero)) :=
      (Int.add_assoc a (ofNat Nat.zero.succ) (ofNat n)).symm.trans (e.trans (Int.add_zero a).symm)
    Nat.succ_ne_zero Nat.zero
      (Nat.eq_zero_of_add_eq_zero (Int.ofNat_inj.mp (Int.add_left_cancel cycle))).left

protected theorem ne_of_lt {a b : Int} (h : a.lt b) : Not (Eq a b) := fun e =>
  Int.lt_irrefl a (Eq.subst (motive := a.lt) e.symm h)

protected theorem ne_of_gt {a b : Int} (h : b.lt a) : Not (Eq a b) := fun e =>
  Int.ne_of_lt h e.symm

theorem lt_iff_add_one_le {a b : Int} : Iff (a.lt b) ((a.add (ofNat Nat.zero.succ)).le b) :=
  Iff.intro (fun h => h) (fun h => h)

protected theorem lt_succ (a : Int) : a.lt (a.add (ofNat Nat.zero.succ)) := Int.le_refl _

theorem natCast_nonneg (n : Nat) : (ofNat Nat.zero).le (ofNat n) :=
  le.intro n (Int.zero_add (ofNat n))

theorem eq_ofNat_of_zero_le {a : Int} (h : (ofNat Nat.zero).le a) :
    Exists (fun n : Nat => Eq a (ofNat n)) :=
  (le.dest_sub h).elim fun n e => Exists.intro n ((Int.sub_zero a).symm.trans e)

theorem natAbs_negOfNat (n : Nat) : Eq (natAbs (negOfNat n)) n :=
  Nat.rec (motive := fun n => Eq (natAbs (negOfNat n)) n) rfl (fun _ _ => rfl) n

theorem natAbs_neg (a : Int) : Eq a.neg.natAbs a.natAbs :=
  Int.rec (motive := fun a => Eq a.neg.natAbs a.natAbs) natAbs_negOfNat (fun _ => rfl) a

theorem natAbs_eq_zero {a : Int} : Iff (Eq a.natAbs Nat.zero) (Eq a (ofNat Nat.zero)) :=
  Iff.intro
    (Int.rec (motive := fun a => Eq a.natAbs Nat.zero → Eq a (ofNat Nat.zero))
      (fun _ h => congrArg ofNat h)
      (fun n h => False.elim (Nat.succ_ne_zero n h)) a)
    (congrArg natAbs)

theorem natAbs_mul (a b : Int) : Eq (a.mul b).natAbs (a.natAbs.mul b.natAbs) :=
  Int.rec (motive := fun a => Eq (a.mul b).natAbs (a.natAbs.mul b.natAbs))
    (fun m => Int.rec (motive := fun b => Eq ((ofNat m).mul b).natAbs (m.mul b.natAbs))
      (fun _ => rfl) (fun n => natAbs_negOfNat (m.mul n.succ)) b)
    (fun m => Int.rec (motive := fun b => Eq ((negSucc m).mul b).natAbs (m.succ.mul b.natAbs))
      (fun n => natAbs_negOfNat (m.succ.mul n)) (fun _ => rfl) b) a

theorem natAbs_mul_self {a : Int} : Eq (ofNat (a.natAbs.mul a.natAbs)) (a.mul a) :=
  Int.rec (motive := fun a => Eq (ofNat (a.natAbs.mul a.natAbs)) (a.mul a))
    (fun _ => rfl) (fun _ => rfl) a

theorem ofNat_succ_pos (n : Nat) : (ofNat Nat.zero).lt (ofNat n.succ) :=
  Nat.rec (motive := fun k => (ofNat Nat.zero).lt (ofNat k.succ))
    (NonNeg.mk _) (fun _ _ => NonNeg.mk _) n

theorem natAbs_natCast (n : Nat) : Eq (ofNat n).natAbs n := Omega.rfl

theorem natAbs_negSucc (n : Nat) : Eq (negSucc n).natAbs n.succ := Omega.rfl

theorem natAbs_zero : Eq (ofNat Nat.zero).natAbs Nat.zero := Omega.rfl

theorem natAbs_one : Eq (ofNat Nat.zero.succ).natAbs Nat.zero.succ := Omega.rfl

theorem toNat_zero : Eq (ofNat Nat.zero).toNat Nat.zero := Omega.rfl

theorem toNat_one : Eq (ofNat Nat.zero.succ).toNat Nat.zero.succ := Omega.rfl

theorem toNat_natCast (n : Nat) : Eq (ofNat n).toNat n := Omega.rfl

theorem toNat_negSucc (n : Nat) : Eq (negSucc n).toNat Nat.zero := Omega.rfl

theorem toNat_neg_natCast (n : Nat) : Eq (ofNat n).neg.toNat Nat.zero :=
  Nat.rec (motive := fun n => Eq (ofNat n).neg.toNat Nat.zero) rfl (fun _ _ => rfl) n

theorem toNat_add_toNat_neg_eq_natAbs (n : Int) : Eq (n.toNat.add n.neg.toNat) n.natAbs :=
  Int.rec (motive := fun n => Eq (n.toNat.add n.neg.toNat) n.natAbs)
    (fun n => congrArg (Nat.add n) (toNat_neg_natCast n))
    (fun n => Nat.zero_add n.succ) n

theorem toNat_sub_toNat_neg (n : Int) : Eq ((ofNat n.toNat).sub (ofNat n.neg.toNat)) n :=
  Int.rec (motive := fun n => Eq ((ofNat n.toNat).sub (ofNat n.neg.toNat)) n)
    (fun n => (congrArg (fun k => (ofNat n).sub (ofNat k)) (toNat_neg_natCast n)).trans
      (Int.sub_zero (ofNat n)))
    (fun n => Int.zero_sub (ofNat n.succ)) n

theorem sign_zero : Eq (ofNat Nat.zero).sign (ofNat Nat.zero) := Omega.rfl

theorem sign_one : Eq (ofNat Nat.zero.succ).sign (ofNat Nat.zero.succ) := Omega.rfl

theorem sign_neg_one : Eq (negSucc Nat.zero).sign (negSucc Nat.zero) := Omega.rfl

theorem sign_natCast_add_one (n : Nat) : Eq ((ofNat n).add (ofNat Nat.zero.succ)).sign
    (ofNat Nat.zero.succ) := Omega.rfl

theorem sign_negSucc (x : Nat) : Eq (negSucc x).sign (negSucc Nat.zero) := Omega.rfl

theorem sign_neg (z : Int) : Eq z.neg.sign z.sign.neg :=
  Int.rec (motive := fun z => Eq z.neg.sign z.sign.neg)
    (fun n => Nat.rec (motive := fun n => Eq (ofNat n).neg.sign (ofNat n).sign.neg)
      rfl (fun _ _ => rfl) n) (fun _ => rfl) z

theorem sign_sign {x : Int} : Eq x.sign.sign x.sign :=
  Int.rec (motive := fun x => Eq x.sign.sign x.sign)
    (fun n => Nat.rec (motive := fun n => Eq (ofNat n).sign.sign (ofNat n).sign)
      rfl (fun _ _ => rfl) n) (fun _ => rfl) x

theorem natAbs_eq (a : Int) : Or (Eq a (ofNat a.natAbs)) (Eq a (ofNat a.natAbs).neg) :=
  Int.rec (motive := fun a => Or (Eq a (ofNat a.natAbs)) (Eq a (ofNat a.natAbs).neg))
    (fun _ => Or.inl rfl) (fun _ => Or.inr rfl) a

end Omega.Int

port_proof Int.natAbs_ofNat' by_reflexivity
port_proof Int.natAbs.eq_1 by_reflexivity
port_proof Int.natAbs.eq_2 by_reflexivity
port_proof Int.toNat.eq_1 by_reflexivity
