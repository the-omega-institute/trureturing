/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude
public import OmegaInit.Data.Int.Basic
import all OmegaInit.Data.Int.Basic
import OmegaInit.Data.Nat.Lemmas

@[expose] public section

namespace Omega.Int

private def ofDifferences (positive negative : Nat) : Int :=
  negOfNat.match_1 (fun _ => Int) negative (fun _ => ofNat positive) negSucc

private theorem subNatNat_zero (a : Nat) : Eq (subNatNat a Nat.zero) (ofNat a) :=
  congrArg (ofDifferences a) (Nat.zero_sub a)

private theorem cancelSuccessors (m n : Nat) : Eq (subNatNat m.succ n.succ) (subNatNat m n) :=
  (congrArg (fun d => ofDifferences d (Nat.sub n.succ m.succ)) (Nat.succ_sub_succ m n)).trans
    (congrArg (ofDifferences (Nat.sub m n)) (Nat.succ_sub_succ n m))

protected theorem subNatNat_eq_coe {m n : Nat} :
    Eq (subNatNat m n) ((ofNat m).sub (ofNat n)) :=
  Nat.rec (motive := fun n => Eq (subNatNat m n) ((ofNat m).sub (ofNat n)))
    ((subNatNat_zero m).trans (congrArg ofNat (Nat.add_zero m).symm))
    (fun _ _ => Omega.rfl) n

theorem subNatNat_add_add (m n k : Nat) :
    Eq (subNatNat (m.add k) (n.add k)) (subNatNat m n) :=
  Nat.rec (motive := fun k => Eq (subNatNat (m.add k) (n.add k)) (subNatNat m n))
    rfl (fun k ih => (cancelSuccessors (m.add k) (n.add k)).trans ih) k

theorem subNatNat_self (n : Nat) : Eq (subNatNat n n) (ofNat Nat.zero) :=
  Nat.rec (motive := fun n => Eq (subNatNat n n) (ofNat Nat.zero))
    rfl (fun n ih => (cancelSuccessors n n).trans ih) n

/-- Split a natural difference according to which argument has the excess. -/
@[elab_as_elim] theorem subNatNat_elim (m n : Nat) (motive : Nat → Nat → Int → Prop)
    (hp : ∀ (i n : Nat), motive (n.add i) n (ofNat i))
    (hn : ∀ (i m : Nat), motive m (m.add i.succ) (negSucc i)) :
    motive m n (subNatNat m n) :=
  (Nat.rec (motive := fun m => ∀ n (P : Nat → Nat → Int → Prop),
    (∀ (i n : Nat), P (n.add i) n (ofNat i)) →
    (∀ (i m : Nat), P m (m.add i.succ) (negSucc i)) →
    P m n (subNatNat m n))
    (fun n P hp hn => Nat.rec (motive := fun n => P Nat.zero n (subNatNat Nat.zero n))
      (hp Nat.zero Nat.zero)
      (fun i _ => Eq.subst (motive := fun y => P Nat.zero y (negSucc i))
        (Nat.zero_add i.succ) (hn i Nat.zero)) n)
    (fun m ih n P hp hn => Nat.rec (motive := fun n => P m.succ n (subNatNat m.succ n))
      (Eq.subst (motive := P m.succ Nat.zero) (subNatNat_zero m.succ).symm
        (Eq.subst (motive := fun x => P x Nat.zero (ofNat m.succ)) (Nat.zero_add m.succ)
          (hp m.succ Nat.zero)))
      (fun n _ => Eq.subst (motive := P m.succ n.succ) (cancelSuccessors m n).symm
        (ih n (fun m n x => P m.succ n.succ x)
          (fun i n => Eq.subst (motive := fun k => P k n.succ (ofNat i))
            (Nat.succ_add n i) (hp i n.succ))
          (fun i m => Eq.subst (motive := fun k => P m.succ k (negSucc i))
            (Nat.succ_add m i.succ) (hn i m.succ)))) n) m) n motive hp hn

theorem subNatNat_add_left {m n : Nat} : Eq (subNatNat (m.add n) m) (ofNat n) :=
  (congrArg (fun k => subNatNat k m) (Nat.add_comm m n)).trans
    ((Eq.subst (motive := fun k => Eq (subNatNat (n.add m) k) (subNatNat n Nat.zero))
      (Nat.zero_add m) (subNatNat_add_add n Nat.zero m)).trans (subNatNat_zero n))

theorem subNatNat_add_right {m n : Nat} : Eq (subNatNat m (m.add n.succ)) (negSucc n) :=
  (congrArg (subNatNat m) (Nat.add_comm m n.succ)).trans
    (Eq.subst (motive := fun k => Eq (subNatNat k (n.succ.add m)) (negSucc n)) (Nat.zero_add m)
      (subNatNat_add_add Nat.zero n.succ m))

protected theorem neg_neg (a : Int) : Eq a.neg.neg a :=
  Int.rec (motive := fun a => Eq a.neg.neg a)
    (fun n => Nat.rec (motive := fun n => Eq (ofNat n).neg.neg (ofNat n))
      rfl (fun _ _ => rfl) n) (fun _ => rfl) a

protected theorem sub_eq_add_neg {a b : Int} : Eq (a.sub b) (a.add b.neg) := Omega.rfl

protected theorem add_zero (a : Int) : Eq (a.add (ofNat Nat.zero)) a :=
  Int.rec (motive := fun a => Eq (a.add (ofNat Nat.zero)) a) (fun _ => rfl) (fun _ => rfl) a

protected theorem add_comm (a b : Int) : Eq (a.add b) (b.add a) :=
  Int.rec (motive := fun a => Eq (a.add b) (b.add a))
    (fun m => Int.rec (motive := fun b => Eq ((ofNat m).add b) (b.add (ofNat m)))
      (fun n => congrArg ofNat (Nat.add_comm m n)) (fun _ => rfl) b)
    (fun m => Int.rec (motive := fun b => Eq ((negSucc m).add b) (b.add (negSucc m)))
      (fun _ => rfl) (fun n => congrArg (fun k : Nat => negSucc k.succ) (Nat.add_comm m n)) b) a

protected theorem zero_add (a : Int) : Eq ((ofNat Nat.zero).add a) a :=
  (Int.add_comm (ofNat Nat.zero) a).trans (Int.add_zero a)

private theorem subNatNat_congr {a b c d : Nat} (h : Eq a b) (g : Eq c d) :
    Eq (subNatNat a c) (subNatNat b d) :=
  (congrArg (fun n => subNatNat n c) h).trans (congrArg (subNatNat b) g)

theorem subNatNat_add (m n k : Nat) :
    Eq (subNatNat (m.add n) k) ((ofNat m).add (subNatNat n k)) :=
  subNatNat_elim n k (fun n k x => Eq (subNatNat (m.add n) k) ((ofNat m).add x))
    (fun i n =>
      (congrArg (fun t => subNatNat t n) ((Nat.add_comm m (n.add i)).trans
        ((Nat.add_assoc n i m).trans (congrArg (Nat.add n) (Nat.add_comm i m))))).trans
        (@subNatNat_add_left n (m.add i)))
    (fun i n =>
      (subNatNat_congr rfl (Nat.add_comm n i.succ)).trans
        (subNatNat_add_add m i.succ n))

theorem subNatNat_add_negSucc (m n k : Nat) :
    Eq ((subNatNat m n).add (negSucc k)) (subNatNat m (n.add k.succ)) :=
  subNatNat_elim m n (fun m n x => Eq (x.add (negSucc k)) (subNatNat m (n.add k.succ)))
    (fun i n =>
      ((subNatNat_congr (Nat.add_comm n i) (Nat.add_comm n k.succ)).trans
        (subNatNat_add_add i k.succ n)).symm)
    (fun i m =>
      ((congrArg (subNatNat m) (Nat.add_assoc m i.succ k.succ)).trans
        ((congrArg (fun t => subNatNat m (m.add t)) (Nat.succ_add i k.succ)).trans
          (@subNatNat_add_right m (i.add k.succ)))).symm)

private theorem add_differences (a b c d : Nat) :
    Eq ((subNatNat a b).add (subNatNat c d)) (subNatNat (a.add c) (b.add d)) :=
  subNatNat_elim c d
    (fun c d x => Eq ((subNatNat a b).add x) (subNatNat (a.add c) (b.add d)))
    (fun i n =>
      (Int.add_comm (subNatNat a b) (ofNat i)).trans
        ((subNatNat_add i a b).symm.trans
          ((subNatNat_add_add (i.add a) b n).symm.trans
            (subNatNat_congr
              ((congrArg (fun t : Nat => t.add n) (Nat.add_comm i a)).trans
                ((Nat.add_right_comm a i n).trans (Nat.add_assoc a n i)))
              rfl))))
    (fun i m =>
      (subNatNat_add_negSucc a b i).trans
        ((subNatNat_add_add a (b.add i.succ) m).symm.trans
          (congrArg (subNatNat (a.add m))
            ((Nat.add_right_comm b i.succ m).trans (Nat.add_assoc b m i.succ)))))

private theorem int_as_difference (a : Int) :
    Exists fun p : Nat => Exists fun n : Nat => Eq a (subNatNat p n) :=
  Int.rec (motive := fun a => Exists fun p : Nat => Exists fun n : Nat => Eq a (subNatNat p n))
    (fun p => Exists.intro p (Exists.intro Nat.zero (subNatNat_zero p).symm))
    (fun n => Exists.intro Nat.zero (Exists.intro n.succ rfl)) a

protected theorem add_assoc (a b c : Int) : Eq ((a.add b).add c) (a.add (b.add c)) :=
  (int_as_difference a).elim fun ap ha => ha.elim fun an ha =>
  (int_as_difference b).elim fun bp hb => hb.elim fun bn hb =>
  (int_as_difference c).elim fun cp hc => hc.elim fun cn hc =>
  Eq.subst (motive := fun a : Int => Eq ((a.add b).add c) (a.add (b.add c))) ha.symm
    (Eq.subst (motive := fun b => Eq (((subNatNat ap an).add b).add c) ((subNatNat ap an).add (b.add c))) hb.symm
      (Eq.subst (motive := fun c => Eq (((subNatNat ap an).add (subNatNat bp bn)).add c)
        ((subNatNat ap an).add ((subNatNat bp bn).add c))) hc.symm
        ((congrArg (fun z : Int => z.add (subNatNat cp cn)) (add_differences ap an bp bn)).trans
          ((add_differences (ap.add bp) (an.add bn) cp cn).trans
            ((subNatNat_congr (Nat.add_assoc ap bp cp) (Nat.add_assoc an bn cn)).trans
              ((add_differences ap an (bp.add cp) (bn.add cn)).symm.trans
                (congrArg ((subNatNat ap an).add) (add_differences bp bn cp cn).symm)))))))

protected theorem add_left_neg (a : Int) : Eq (a.neg.add a) (ofNat Nat.zero) :=
  Int.rec (motive := fun a => Eq (a.neg.add a) (ofNat Nat.zero))
    (fun n => Nat.rec (motive := fun n => Eq ((ofNat n).neg.add (ofNat n)) (ofNat Nat.zero))
      rfl (fun n _ => subNatNat_self n.succ) n)
    (fun n => subNatNat_self n.succ) a

protected theorem add_right_neg (a : Int) : Eq (a.add a.neg) (ofNat Nat.zero) :=
  (Int.add_comm a a.neg).trans (Int.add_left_neg a)

protected theorem add_right_comm (a b c : Int) : Eq ((a.add b).add c) ((a.add c).add b) :=
  (Int.add_assoc a b c).trans ((congrArg a.add (Int.add_comm b c)).trans (Int.add_assoc a c b).symm)

protected theorem neg_add_cancel_left (a b : Int) : Eq (a.neg.add (a.add b)) b :=
  (Int.add_assoc a.neg a b).symm.trans
    ((congrArg (fun t : Int => t.add b) (Int.add_left_neg a)).trans (Int.zero_add b))

protected theorem add_left_cancel {a b c : Int} (h : Eq (a.add b) (a.add c)) : Eq b c :=
  (Int.neg_add_cancel_left a b).symm.trans
    ((congrArg a.neg.add h).trans (Int.neg_add_cancel_left a c))

protected theorem neg_eq_of_add_eq_zero {a b : Int} (h : Eq (a.add b) (ofNat Nat.zero)) :
    Eq a.neg b :=
  Int.add_left_cancel ((Int.add_right_neg a).trans h.symm)

protected theorem neg_add {a b : Int} : Eq (a.add b).neg (a.neg.add b.neg) :=
  have inner : Eq (b.add (a.neg.add b.neg)) a.neg :=
    (Int.add_assoc b a.neg b.neg).symm.trans
      ((congrArg (fun t : Int => t.add b.neg) (Int.add_comm b a.neg)).trans
        ((Int.add_assoc a.neg b b.neg).trans
          ((congrArg a.neg.add (Int.add_right_neg b)).trans (Int.add_zero a.neg))))
  Int.neg_eq_of_add_eq_zero
    ((Int.add_assoc a b (a.neg.add b.neg)).trans
      ((congrArg a.add inner).trans (Int.add_right_neg a)))

protected theorem mul_comm (a b : Int) : Eq (a.mul b) (b.mul a) :=
  Int.rec (motive := fun a => Eq (a.mul b) (b.mul a))
    (fun m => Int.rec (motive := fun b => Eq ((ofNat m).mul b) (b.mul (ofNat m)))
      (fun n => congrArg ofNat (Nat.mul_comm m n))
      (fun n => congrArg negOfNat (Nat.mul_comm m n.succ)) b)
    (fun m => Int.rec (motive := fun b => Eq ((negSucc m).mul b) (b.mul (negSucc m)))
      (fun n => congrArg negOfNat (Nat.mul_comm m.succ n))
      (fun n => congrArg ofNat (Nat.mul_comm m.succ n.succ)) b) a

protected theorem mul_zero (a : Int) : Eq (a.mul (ofNat Nat.zero)) (ofNat Nat.zero) :=
  Int.rec (motive := fun a => Eq (a.mul (ofNat Nat.zero)) (ofNat Nat.zero)) (fun _ => rfl) (fun _ => rfl) a

protected theorem zero_mul (a : Int) : Eq ((ofNat Nat.zero).mul a) (ofNat Nat.zero) :=
  (Int.mul_comm (ofNat Nat.zero) a).trans (Int.mul_zero a)

protected theorem mul_one (a : Int) : Eq (a.mul (ofNat (Nat.succ Nat.zero))) a :=
  Int.rec (motive := fun a => Eq (a.mul (ofNat (Nat.succ Nat.zero))) a)
    (fun n => congrArg ofNat (Nat.mul_one n))
    (fun n => congrArg negOfNat (Nat.mul_one n.succ)) a

protected theorem one_mul (a : Int) : Eq ((ofNat (Nat.succ Nat.zero)).mul a) a :=
  (Int.mul_comm (ofNat (Nat.succ Nat.zero)) a).trans (Int.mul_one a)

theorem ofNat_mul_negOfNat (m n : Nat) :
    Eq ((ofNat m).mul (negOfNat n)) (negOfNat (m.mul n)) :=
  Nat.rec (motive := fun n => Eq ((ofNat m).mul (negOfNat n)) (negOfNat (m.mul n)))
    rfl (fun _ _ => rfl) n

theorem negOfNat_mul_ofNat (m n : Nat) :
    Eq ((negOfNat m).mul (ofNat n)) (negOfNat (m.mul n)) :=
  (Int.mul_comm (negOfNat m) (ofNat n)).trans
    ((ofNat_mul_negOfNat n m).trans (congrArg negOfNat (Nat.mul_comm n m)))

theorem negSucc_mul_negOfNat (m n : Nat) :
    Eq ((negSucc m).mul (negOfNat n)) (ofNat (m.succ.mul n)) :=
  Nat.rec (motive := fun n => Eq ((negSucc m).mul (negOfNat n)) (ofNat (m.succ.mul n)))
    rfl (fun _ _ => rfl) n

theorem negOfNat_mul_negSucc (m n : Nat) :
    Eq ((negOfNat n).mul (negSucc m)) (ofNat (n.mul m.succ)) :=
  (Int.mul_comm (negOfNat n) (negSucc m)).trans
    ((negSucc_mul_negOfNat m n).trans (congrArg ofNat (Nat.mul_comm m.succ n)))

protected theorem mul_assoc (a b c : Int) : Eq ((a.mul b).mul c) (a.mul (b.mul c)) :=
  let P := fun (a b c : Int) => Eq ((a.mul b).mul c) (a.mul (b.mul c))
  Int.rec (motive := fun a => P a b c)
    (fun m => Int.rec (motive := fun b => P (ofNat m) b c)
      (fun n => Int.rec (motive := fun c => P (ofNat m) (ofNat n) c)
        (fun k => congrArg ofNat (Nat.mul_assoc m n k))
        (fun k => (congrArg negOfNat (Nat.mul_assoc m n k.succ)).trans
          (ofNat_mul_negOfNat m (n.mul k.succ)).symm) c)
      (fun n => Int.rec (motive := fun c => P (ofNat m) (negSucc n) c)
        (fun k => (negOfNat_mul_ofNat (m.mul n.succ) k).trans
          ((congrArg negOfNat (Nat.mul_assoc m n.succ k)).trans
            (ofNat_mul_negOfNat m (n.succ.mul k)).symm))
        (fun k => (negOfNat_mul_negSucc k (m.mul n.succ)).trans
          (congrArg ofNat (Nat.mul_assoc m n.succ k.succ))) c) b)
    (fun m => Int.rec (motive := fun b => P (negSucc m) b c)
      (fun n => Int.rec (motive := fun c => P (negSucc m) (ofNat n) c)
        (fun k => (negOfNat_mul_ofNat (m.succ.mul n) k).trans
          (congrArg negOfNat (Nat.mul_assoc m.succ n k)))
        (fun k => (negOfNat_mul_negSucc k (m.succ.mul n)).trans
          ((congrArg ofNat (Nat.mul_assoc m.succ n k.succ)).trans
            (negSucc_mul_negOfNat m (n.mul k.succ)).symm)) c)
      (fun n => Int.rec (motive := fun c => P (negSucc m) (negSucc n) c)
        (fun k => (congrArg ofNat (Nat.mul_assoc m.succ n.succ k)).trans
          (negSucc_mul_negOfNat m (n.succ.mul k)).symm)
        (fun k => congrArg negOfNat (Nat.mul_assoc m.succ n.succ k.succ)) c) b) a

protected theorem neg_mul (a b : Int) : Eq (a.neg.mul b) (a.mul b).neg :=
  Int.rec (motive := fun a => Eq (a.neg.mul b) (a.mul b).neg)
    (fun m => Int.rec (motive := fun b => Eq ((ofNat m).neg.mul b) ((ofNat m).mul b).neg)
      (fun n => negOfNat_mul_ofNat m n)
      (fun n => (negOfNat_mul_negSucc n m).trans (Int.neg_neg (ofNat (m.mul n.succ))).symm) b)
    (fun m => Int.rec (motive := fun b => Eq ((negSucc m).neg.mul b) ((negSucc m).mul b).neg)
      (fun n => (Int.neg_neg (ofNat (m.succ.mul n))).symm)
      (fun _ => rfl) b) a

protected theorem mul_neg (a b : Int) : Eq (a.mul b.neg) (a.mul b).neg :=
  (Int.mul_comm a b.neg).trans ((Int.neg_mul b a).trans (congrArg Int.neg (Int.mul_comm b a)))

protected theorem neg_mul_neg (a b : Int) : Eq (a.neg.mul b.neg) (a.mul b) :=
  (Int.neg_mul a b.neg).trans
    ((congrArg Int.neg (Int.mul_neg a b)).trans (Int.neg_neg (a.mul b)))

private theorem neg_shift (m n : Nat) : Eq (subNatNat m (m.add n)) (negOfNat n) :=
  Nat.rec (motive := fun n => Eq (subNatNat m (m.add n)) (negOfNat n))
    (subNatNat_self m) (fun n _ => @subNatNat_add_right m n) n

theorem ofNat_mul_subNatNat (m n k : Nat) :
    Eq ((ofNat m).mul (subNatNat n k)) (subNatNat (m.mul n) (m.mul k)) :=
  subNatNat_elim n k (fun n k x => Eq ((ofNat m).mul x) (subNatNat (m.mul n) (m.mul k)))
    (fun i n => ((congrArg (fun t => subNatNat t (m.mul n)) (Nat.mul_add m n i)).trans
      (@subNatNat_add_left (m.mul n) (m.mul i))).symm)
    (fun i n => ((congrArg (subNatNat (m.mul n)) (Nat.mul_add m n i.succ)).trans
      (neg_shift (m.mul n) (m.mul i.succ))).symm)

private theorem ofNat_mul_add (m : Nat) (a b : Int) :
    Eq ((ofNat m).mul (a.add b)) (((ofNat m).mul a).add ((ofNat m).mul b)) :=
  let k := ofNat m
  (int_as_difference a).elim fun ap ha => ha.elim fun an ha =>
  (int_as_difference b).elim fun bp hb => hb.elim fun bn hb =>
  let x := subNatNat ap an
  let P := fun (a b : Int) => Eq (k.mul (a.add b)) ((k.mul a).add (k.mul b))
  Eq.subst (motive := fun t => P t b) ha.symm (Eq.subst (motive := P x) hb.symm
    ((congrArg k.mul (add_differences ap an bp bn)).trans
      ((ofNat_mul_subNatNat m (ap.add bp) (an.add bn)).trans
        ((subNatNat_congr (Nat.mul_add m ap bp) (Nat.mul_add m an bn)).trans
          ((add_differences (m.mul ap) (m.mul an) (m.mul bp) (m.mul bn)).symm.trans
            ((congrArg (fun t : Int => t.add (subNatNat (m.mul bp) (m.mul bn)))
              (ofNat_mul_subNatNat m ap an).symm).trans
              (congrArg (k.mul x).add (ofNat_mul_subNatNat m bp bn).symm)))))))

protected theorem mul_add (a b c : Int) : Eq (a.mul (b.add c)) ((a.mul b).add (a.mul c)) :=
  Int.rec (motive := fun a => Eq (a.mul (b.add c)) ((a.mul b).add (a.mul c)))
    (fun m => ofNat_mul_add m b c)
    (fun m =>
      let k := ofNat m.succ
      (Int.neg_mul k (b.add c)).trans
        ((congrArg Int.neg (ofNat_mul_add m.succ b c)).trans
          (Int.neg_add.trans
            ((congrArg (fun t : Int => t.add (k.mul c).neg) (Int.neg_mul k b).symm).trans
              (congrArg (k.neg.mul b).add (Int.neg_mul k c).symm))))) a

protected theorem add_mul (a b c : Int) : Eq ((a.add b).mul c) ((a.mul c).add (b.mul c)) :=
  (Int.mul_comm (a.add b) c).trans
    ((Int.mul_add c a b).trans
      ((congrArg (fun t : Int => t.add (c.mul b)) (Int.mul_comm c a)).trans
        (congrArg (a.mul c).add (Int.mul_comm c b))))

protected theorem mul_right_comm (a b c : Int) : Eq ((a.mul b).mul c) ((a.mul c).mul b) :=
  (Int.mul_assoc a b c).trans ((congrArg a.mul (Int.mul_comm b c)).trans (Int.mul_assoc a c b).symm)

protected theorem mul_sub (a b c : Int) : Eq (a.mul (b.sub c)) ((a.mul b).sub (a.mul c)) :=
  (Int.mul_add a b c.neg).trans (congrArg (a.mul b).add (Int.mul_neg a c))

protected theorem sub_mul (a b c : Int) : Eq ((a.sub b).mul c) ((a.mul c).sub (b.mul c)) :=
  (Int.add_mul a b.neg c).trans (congrArg (a.mul c).add (Int.neg_mul b c))

protected theorem sub_self (a : Int) : Eq (a.sub a) (ofNat Nat.zero) := Int.add_right_neg a

protected theorem sub_eq_zero {a b : Int} : Iff (Eq (a.sub b) (ofNat Nat.zero)) (Eq a b) :=
  Iff.intro
    (fun h => Int.add_left_cancel (a := b.neg)
      ((Int.add_comm b.neg a).trans (h.trans (Int.add_left_neg b).symm)))
    (fun h => Eq.subst (motive := fun t => Eq (a.sub t) (ofNat Nat.zero)) h (Int.sub_self a))

theorem negSucc_ne_zero (n : Nat) : Not (Eq (negSucc n) (ofNat Nat.zero)) :=
  fun e => Eq.subst
    (motive := fun x => Int.rec (motive := fun _ => Prop) (fun _ => False) (fun _ => True) x) e True.intro

theorem ofNat_inj {m n : Nat} : Iff (Eq (ofNat m) (ofNat n)) (Eq m n) :=
  Iff.intro (congrArg natAbs) (congrArg ofNat)

private theorem negOfNat_eq_zero {n : Nat} (h : Eq (negOfNat n) (ofNat Nat.zero)) :
    Eq n Nat.zero :=
  (Nat.rec (motive := fun n => Eq (negOfNat n) (ofNat Nat.zero) → Eq n Nat.zero)
    (fun _ => rfl) (fun n _ h => False.elim (negSucc_ne_zero n h)) n) h

protected theorem mul_eq_zero {a b : Int} :
    Iff (Eq (a.mul b) (ofNat Nat.zero)) (Or (Eq a (ofNat Nat.zero)) (Eq b (ofNat Nat.zero))) :=
  let zero := ofNat Nat.zero
  let P := fun (a b : Int) => Eq (a.mul b) zero → Or (Eq a zero) (Eq b zero)
  Iff.intro
    (Int.rec (motive := fun a => P a b)
      (fun m => Int.rec (motive := fun b => P (ofNat m) b)
        (fun _ h => (Nat.mul_eq_zero.mp (ofNat_inj.mp h)).elim
          (fun hm => Or.inl (congrArg ofNat hm)) (fun hn => Or.inr (congrArg ofNat hn)))
        (fun n h => (Nat.mul_eq_zero.mp (negOfNat_eq_zero h)).elim
          (fun hm => Or.inl (congrArg ofNat hm)) (fun hn => False.elim (Nat.succ_ne_zero n hn))) b)
      (fun m => Int.rec (motive := fun b => P (negSucc m) b)
        (fun _ h => (Nat.mul_eq_zero.mp (negOfNat_eq_zero h)).elim
          (fun hm => False.elim (Nat.succ_ne_zero m hm)) (fun hn => Or.inr (congrArg ofNat hn)))
        (fun n h => False.elim
          ((Nat.mul_eq_zero.mp (ofNat_inj.mp h)).elim (Nat.succ_ne_zero m) (Nat.succ_ne_zero n))) b) a)
    (fun h => h.elim
      (fun ha => Eq.subst (motive := fun a => Eq (Int.mul a b) zero) ha.symm (Int.zero_mul b))
      (fun hb => Eq.subst (motive := fun b => Eq (a.mul b) zero) hb.symm (Int.mul_zero a)))

protected theorem mul_ne_zero {a b : Int}
    (a0 : Not (Eq a (ofNat Nat.zero))) (b0 : Not (Eq b (ofNat Nat.zero))) :
    Not (Eq (a.mul b) (ofNat Nat.zero)) :=
  fun h => (Int.mul_eq_zero.mp h).elim a0 b0

protected theorem eq_of_mul_eq_mul_right {a b c : Int}
    (ha : Not (Eq a (ofNat Nat.zero))) (h : Eq (b.mul a) (c.mul a)) : Eq b c :=
  have hz := (Int.sub_mul b c a).trans (Int.sub_eq_zero.mpr h)
  Int.sub_eq_zero.mp ((Int.mul_eq_zero.mp hz).elim (fun e => e) (fun e => False.elim (ha e)))

protected theorem eq_of_mul_eq_mul_left {a b c : Int}
    (ha : Not (Eq a (ofNat Nat.zero))) (h : Eq (a.mul b) (a.mul c)) : Eq b c :=
  Int.eq_of_mul_eq_mul_right ha ((Int.mul_comm b a).trans (h.trans (Int.mul_comm a c)))

protected theorem neg_zero : Eq (ofNat Nat.zero).neg (ofNat Nat.zero) := Omega.rfl

theorem neg_ofNat_succ (n : Nat) : Eq (ofNat n.succ).neg (negSucc n) := Omega.rfl

theorem neg_negSucc (n : Nat) : Eq (negSucc n).neg (ofNat n.succ) := Omega.rfl

theorem ofNat_add_ofNat (m n : Nat) : Eq ((ofNat m).add (ofNat n)) (ofNat (m.add n)) := Omega.rfl

theorem ofNat_add_negSucc (m n : Nat) :
    Eq ((ofNat m).add (negSucc n)) (subNatNat m n.succ) := Omega.rfl

theorem negSucc_add_ofNat (m n : Nat) :
    Eq ((negSucc m).add (ofNat n)) (subNatNat n m.succ) := Omega.rfl

theorem negSucc_add_negSucc (m n : Nat) :
    Eq ((negSucc m).add (negSucc n)) (negSucc (m.add n).succ) := Omega.rfl

theorem ofNat_mul_ofNat (m n : Nat) : Eq ((ofNat m).mul (ofNat n)) (ofNat (m.mul n)) := Omega.rfl

theorem ofNat_mul_negSucc (m n : Nat) :
    Eq ((ofNat m).mul (negSucc n)) (ofNat (m.mul n.succ)).neg := Omega.rfl

theorem negSucc_mul_ofNat (m n : Nat) :
    Eq ((negSucc m).mul (ofNat n)) (ofNat (m.succ.mul n)).neg := Omega.rfl

theorem negSucc_mul_negSucc (m n : Nat) :
    Eq ((negSucc m).mul (negSucc n)) (ofNat (m.succ.mul n.succ)) := Omega.rfl

theorem negSucc_inj {m n : Nat} : Iff (Eq (negSucc m) (negSucc n)) (Eq m n) :=
  Iff.intro (fun h => Nat.succ.inj (congrArg natAbs h)) (congrArg negSucc)

theorem wlog_sign {P : Int → Prop} (inv : ∀ i, Iff (P i) (P i.neg))
    (w : ∀ n : Nat, P (ofNat n)) (i : Int) : P i :=
  Int.rec (motive := P) w (fun n => (inv (ofNat n.succ)).mp (w n.succ)) i

protected theorem sub_zero (a : Int) : Eq (a.sub (ofNat Nat.zero)) a := Int.add_zero a

protected theorem zero_sub (a : Int) : Eq ((ofNat Nat.zero).sub a) a.neg := Int.zero_add a.neg

protected theorem sub_sub (a b c : Int) : Eq ((a.sub b).sub c) (a.sub (b.add c)) :=
  (Int.add_assoc a b.neg c.neg).trans (congrArg a.add Int.neg_add.symm)

protected theorem neg_sub (a b : Int) : Eq (a.sub b).neg (b.sub a) :=
  Int.neg_add.trans ((congrArg a.neg.add (Int.neg_neg b)).trans (Int.add_comm a.neg b))

protected theorem sub_add_cancel (a b : Int) : Eq ((a.sub b).add b) a :=
  (Int.add_assoc a b.neg b).trans ((congrArg a.add (Int.add_left_neg b)).trans (Int.add_zero a))

protected theorem add_sub_cancel (a b : Int) : Eq ((a.add b).sub b) a :=
  (Int.add_assoc a b b.neg).trans ((congrArg a.add (Int.add_right_neg b)).trans (Int.add_zero a))

theorem ofNat_sub {m n : Nat} (h : Nat.le m n) : Eq (ofNat (Nat.sub n m)) ((ofNat n).sub (ofNat m)) :=
  (Nat.le.dest h).elim fun k e =>
    Eq.subst (motive := fun n => Eq (ofNat (Nat.sub n m)) ((ofNat n).sub (ofNat m))) e
      ((congrArg ofNat (Nat.add_sub_cancel_left m k)).trans
        (subNatNat_add_left.symm.trans Int.subNatNat_eq_coe))

private theorem subNatNat_eq_cases (m n : Nat) : Eq (subNatNat m n)
    (Nat.casesOn (motive := fun _ => Int) (Nat.sub n m) (ofNat (Nat.sub m n)) negSucc) :=
  subNatNat_elim m n (fun m n i => Eq i
      (Nat.casesOn (motive := fun _ => Int) (Nat.sub n m) (ofNat (Nat.sub m n)) negSucc))
    (fun i n =>
      (congrArg ofNat (Nat.add_sub_cancel_left n i)).symm.trans
        (congrArg (fun k : Nat => Nat.casesOn (motive := fun _ => Int) k
          (ofNat (Nat.sub (Nat.add n i) n)) negSucc) (Nat.sub_self_add n i)).symm)
    (fun i m => (congrArg (fun k : Nat => Nat.casesOn (motive := fun _ => Int) k
      (ofNat (Nat.sub m (Nat.add m i.succ))) negSucc) (Nat.add_sub_cancel_left m i.succ)).symm)

end Omega.Int

port_proof Int.subNatNat.eq_1 using Omega.Int.subNatNat_eq_cases
port_proof Ne.eq_1 by_reflexivity

port_proof Int.natCast_zero by_reflexivity
port_proof Int.natCast_one by_reflexivity
port_proof Int.natCast_add by_reflexivity
port_proof Int.natCast_add_one by_reflexivity

port_proof Int.add_neg_cancel_right
port_proof Int.negSucc_eq
port_proof Int.sub_sub_self by_constructive_casts

port_proof Int.add_left_comm

port_proof Int.natCast_mul

port_proof Int.neg_inj

port_proof Int.mul_left_comm

port_proof Int.neg_mul_eq_mul_neg
