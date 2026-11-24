/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Data.Int

/-!
Omega original.

Exact signed fractions. Denominators are positive by construction, and arithmetic
with an undefined operand is undefined.
-/

noncomputable section

@[expose] public section

namespace Omega

inductive IntRatio where
  | undefined
  | fraction (num : Int) (denPred : Nat)

namespace IntRatio

def value (numerator : Int) (denominator : Nat) : IntRatio :=
  Nat.rec undefined (fun pred _ => fraction numerator pred) denominator

def ofInt (n : Int) : IntRatio := fraction n Nat.zero

/-- Embed the positive denominator represented by its predecessor. -/
def denominator (pred : Nat) : Int := Int.ofNat pred.succ

/-- The predecessor of the product of two positive denominators. -/
def mulDenPred (a b : Nat) : Nat := (a.succ.mul b).add a

theorem denominator_mul (a b : Nat) :
    Eq (denominator (mulDenPred a b)) ((denominator a).mul (denominator b)) := Eq.refl

/-- Cross multiplication on finite fractions. The undefined value agrees only with itself. -/
def Equivalent (x y : IntRatio) : Prop :=
  IntRatio.rec (motive := fun _ => Prop)
    (IntRatio.rec (motive := fun _ => Prop) True (fun _ _ => False) y)
    (fun a b => IntRatio.rec (motive := fun _ => Prop) False
      (fun c d => Eq (a.mul (denominator d)) (c.mul (denominator b))) y) x

theorem equivalent_refl (x : IntRatio) : Equivalent x x :=
  IntRatio.rec (motive := fun x => Equivalent x x) True.intro (fun _ _ => Eq.refl) x

theorem Equivalent.symm {x y : IntRatio} (h : Equivalent x y) : Equivalent y x :=
  let P := fun x y => Equivalent x y → Equivalent y x
  (IntRatio.rec (motive := fun x => P x y)
    (IntRatio.rec (motive := fun y => P undefined y) (fun h => h) (fun _ _ h => h) y)
    (fun a b => IntRatio.rec (motive := fun y => P (fraction a b) y)
      (fun h => h) (fun _ _ h => Eq.symm h) y) x) h

private theorem cross_trans (a b c d e f : Int) (hd : Not (Eq d Int.zero))
    (h : Eq (a.mul d) (c.mul b)) (g : Eq (c.mul f) (e.mul d)) :
    Eq (a.mul f) (e.mul b) :=
  Int.eq_of_mul_eq_mul_right hd
    ((Int.mul_right_comm a f d).trans
      ((congrArg (fun t : Int => t.mul f) h).trans
        ((Int.mul_right_comm c b f).trans
          ((congrArg (fun t : Int => t.mul b) g).trans (Int.mul_right_comm e d b)))))

theorem Equivalent.trans {x y z : IntRatio}
    (h : Equivalent x y) (g : Equivalent y z) : Equivalent x z :=
  let P := fun x y z => Equivalent x y → Equivalent y z → Equivalent x z
  (IntRatio.rec (motive := fun y => P x y z)
    (IntRatio.rec (motive := fun x => P x undefined z) (fun _ g => g)
      (fun _ _ h _ => False.elim h) x)
    (fun c d => IntRatio.rec (motive := fun x => P x (fraction c d) z)
      (fun h _ => False.elim h)
      (fun a b => IntRatio.rec (motive := fun z => P (fraction a b) (fraction c d) z)
        (fun _ g => False.elim g)
        (fun e f => cross_trans a (denominator b) c (denominator d) e (denominator f)
          (Int.ofNat_succ_ne_zero d)) z) x) y) h g

/-- Apply a binary operation on the finite part, propagating undefined operands. -/
def map₂ (f : Int → Nat → Int → Nat → IntRatio) (x y : IntRatio) : IntRatio :=
  IntRatio.rec undefined
    (fun a b => IntRatio.rec undefined (fun c d => f a b c d) y) x

def add (x y : IntRatio) : IntRatio :=
  map₂ (fun a b c d =>
    fraction ((a.mul (denominator d)).add (c.mul (denominator b))) (mulDenPred b d)) x y

def neg (x : IntRatio) : IntRatio :=
  IntRatio.rec undefined (fun a b => fraction a.neg b) x

def sub (x y : IntRatio) : IntRatio := add x (neg y)

def mul (x y : IntRatio) : IntRatio :=
  map₂ (fun a b c d => fraction (a.mul c) (mulDenPred b d)) x y

def inv (x : IntRatio) : IntRatio :=
  IntRatio.rec undefined (fun a b =>
    Int.rec
      (fun n => value (denominator b) n)
      (fun n => fraction (denominator b).neg n) a) x

/-- Finite ratios are ordered by their signed cross products. -/
def Le (x y : IntRatio) : Prop :=
  IntRatio.rec (motive := fun _ => Prop) False
    (fun a b => IntRatio.rec (motive := fun _ => Prop) False
      (fun c d => (a.mul (denominator d)).le (c.mul (denominator b))) y) x

def Lt (x y : IntRatio) : Prop := And (Le x y) (Not (Equivalent x y))

theorem value_undefined_iff (a : Int) (n : Nat) :
    Iff (Eq (value a n) undefined) (Eq n Nat.zero) :=
  Iff.intro
    (Nat.rec (motive := fun n => Eq (value a n) undefined → Eq n Nat.zero)
      (fun _ => Eq.refl)
      (fun _ _ h => False.elim (Eq.subst
        (fun x => IntRatio.rec (motive := fun _ => Prop) False (fun _ _ => True) x)
        h True.intro)) n)
    (fun h => Eq.subst (fun n => Eq (value a n) undefined) h.symm Eq.refl)

theorem value_scale (a : Int) (d k : Nat) :
    Equivalent (value (a.mul (denominator k)) (d.mul k.succ)) (value a d) :=
  Nat.rec (motive := fun d =>
    Equivalent (value (a.mul (denominator k)) (d.mul k.succ)) (value a d))
    (Eq.subst (fun d => Equivalent (value (a.mul (denominator k)) d) undefined)
      (Nat.zero_mul k.succ).symm True.intro)
    (fun d _ =>
      (Int.mul_right_comm a (denominator k) (denominator d)).trans
        (Int.mul_assoc a (denominator d) (denominator k))) d

theorem ofInt_congr {a b : Int} (h : Eq a b) : Equivalent (ofInt a) (ofInt b) :=
  congrArg (fun t : Int => t.mul Int.one) h

theorem neg_congr {x y : IntRatio} (h : Equivalent x y) : Equivalent x.neg y.neg :=
  let P := fun (x y : IntRatio) => Equivalent x y → Equivalent x.neg y.neg
  (IntRatio.rec (motive := fun x => P x y)
    (IntRatio.rec (motive := fun y => P undefined y) (fun h => h) (fun _ _ h => h) y)
    (fun a b => IntRatio.rec (motive := fun y => P (fraction a b) y)
      (fun h => h)
      (fun c d h => (Int.neg_mul a (denominator d)).trans
        ((congrArg Int.neg h).trans (Int.neg_mul c (denominator b)).symm)) y) x) h

theorem add_comm (x y : IntRatio) : Equivalent (x.add y) (y.add x) :=
  let P := fun (x y : IntRatio) => Equivalent (x.add y) (y.add x)
  IntRatio.rec (motive := fun x => P x y)
    (IntRatio.rec (motive := fun y => P undefined y) True.intro (fun _ _ => True.intro) y)
    (fun a b => IntRatio.rec (motive := fun y => P (fraction a b) y)
      True.intro (fun c d => Eq.map₂ Int.mul
        (Int.add_comm (a.mul (denominator d)) (c.mul (denominator b)))
        (Int.mul_comm (denominator d) (denominator b))) y) x

theorem mul_comm (x y : IntRatio) : Equivalent (x.mul y) (y.mul x) :=
  let P := fun (x y : IntRatio) => Equivalent (x.mul y) (y.mul x)
  IntRatio.rec (motive := fun x => P x y)
    (IntRatio.rec (motive := fun y => P undefined y) True.intro (fun _ _ => True.intro) y)
    (fun a b => IntRatio.rec (motive := fun y => P (fraction a b) y)
      True.intro (fun c d => Eq.map₂ Int.mul (Int.mul_comm a c)
        (Int.mul_comm (denominator d) (denominator b))) y) x

theorem add_zero (x : IntRatio) : Equivalent (x.add (ofInt Int.zero)) x :=
  IntRatio.rec (motive := fun x => Equivalent (x.add (ofInt Int.zero)) x)
    True.intro (fun a b =>
      let d := denominator b
      Eq.map₂ Int.mul
        ((Eq.map₂ Int.add (Int.mul_one a) (Int.zero_mul d)).trans (Int.add_zero a))
        (Int.mul_one d).symm) x

theorem mul_one (x : IntRatio) : Equivalent (x.mul (ofInt Int.one)) x :=
  IntRatio.rec (motive := fun x => Equivalent (x.mul (ofInt Int.one)) x)
    True.intro (fun a b => Eq.map₂ Int.mul (Int.mul_one a) (Int.mul_one (denominator b)).symm) x

private theorem map₂_congr_left (f : Int → Nat → Int → Nat → IntRatio)
    (finite : ∀ (a c t : Int) (b d u : Nat), Equivalent (fraction a b) (fraction c d) →
      Equivalent (f a b t u) (f c d t u))
    {x y : IntRatio} (h : Equivalent x y) (z : IntRatio) :
    Equivalent (map₂ f x z) (map₂ f y z) :=
  let P := fun x y => Equivalent x y → Equivalent (map₂ f x z) (map₂ f y z)
  (IntRatio.rec (motive := fun x => P x y)
    (IntRatio.rec (motive := fun y => P undefined y)
      (fun _ => True.intro) (fun _ _ h => False.elim h) y)
    (fun a b => IntRatio.rec (motive := fun y => P (fraction a b) y)
      (fun h => False.elim h)
      (fun c d h => IntRatio.rec
        (motive := fun z => Equivalent (map₂ f (fraction a b) z) (map₂ f (fraction c d) z))
        True.intro (fun t u => finite a c t b d u h) z) y) x) h

private theorem add_cross_left (a b c d t u : Int) (h : Eq (a.mul d) (c.mul b)) :
    Eq (((a.mul u).add (t.mul b)).mul (d.mul u))
      (((c.mul u).add (t.mul d)).mul (b.mul u)) :=
  have numer := (Int.mul_mul_mul_comm a u d u).trans
    ((congrArg (fun k : Int => k.mul (u.mul u)) h).trans (Int.mul_mul_mul_comm c u b u).symm)
  have offset := Int.mul_mul_mul_comm t b d u
  (Int.add_mul (a.mul u) (t.mul b) (d.mul u)).trans
    ((Eq.map₂ Int.add numer offset).trans (Int.add_mul (c.mul u) (t.mul d) (b.mul u)).symm)

theorem add_congr_left {x y : IntRatio} (h : Equivalent x y) (z : IntRatio) :
    Equivalent (x.add z) (y.add z) :=
  map₂_congr_left
    (fun a b c d => fraction ((a.mul (denominator d)).add (c.mul (denominator b))) (mulDenPred b d))
    (fun a c t b d u => add_cross_left a (denominator b) c (denominator d) t (denominator u))
    h z

theorem add_congr {x y z w : IntRatio} (h : Equivalent x y) (g : Equivalent z w) :
    Equivalent (x.add z) (y.add w) :=
  (add_congr_left h z).trans ((add_comm y z).trans ((add_congr_left g y).trans (add_comm w y)))

theorem sub_congr {x y z w : IntRatio} (h : Equivalent x y) (g : Equivalent z w) :
    Equivalent (x.sub z) (y.sub w) := add_congr h (neg_congr g)

theorem mul_congr_left {x y : IntRatio} (h : Equivalent x y) (z : IntRatio) :
    Equivalent (x.mul z) (y.mul z) :=
  map₂_congr_left (fun a b c d => fraction (a.mul c) (mulDenPred b d))
    (fun a c t b d u eq =>
      (Int.mul_mul_mul_comm a t (denominator d) (denominator u)).trans
        ((congrArg (fun k : Int => k.mul (t.mul (denominator u))) eq).trans
          (Int.mul_mul_mul_comm c t (denominator b) (denominator u)).symm))
    h z

theorem mul_congr {x y z w : IntRatio} (h : Equivalent x y) (g : Equivalent z w) :
    Equivalent (x.mul z) (y.mul w) :=
  (mul_congr_left h z).trans ((mul_comm y z).trans ((mul_congr_left g y).trans (mul_comm w y)))

private theorem mul_add_cross (a b c d e f : Int) :
    Eq ((a.mul ((c.mul f).add (e.mul d))).mul ((b.mul d).mul (b.mul f)))
      ((((a.mul c).mul (b.mul f)).add ((a.mul e).mul (b.mul d))).mul (b.mul (d.mul f))) :=
  have common : Eq ((b.mul d).mul (b.mul f)) (b.mul (b.mul (d.mul f))) :=
    (Int.mul_mul_mul_comm b d b f).trans (Int.mul_assoc b b (d.mul f))
  have left := Eq.map₂ Int.mul (Int.mul_add a (c.mul f) (e.mul d)) common
  have right : Eq (((a.mul c).mul (b.mul f)).add ((a.mul e).mul (b.mul d)))
      (((a.mul (c.mul f)).add (a.mul (e.mul d))).mul b) :=
    (Eq.map₂ Int.add
      ((Int.mul_assoc (a.mul c) b f).symm.trans
        ((Int.mul_right_comm (a.mul c) b f).trans
          (congrArg (fun t : Int => t.mul b) (Int.mul_assoc a c f))))
      ((Int.mul_assoc (a.mul e) b d).symm.trans
        ((Int.mul_right_comm (a.mul e) b d).trans
          (congrArg (fun t : Int => t.mul b) (Int.mul_assoc a e d))))).trans
      (Int.add_mul (a.mul (c.mul f)) (a.mul (e.mul d)) b).symm
  left.trans
    (((Int.mul_assoc ((a.mul (c.mul f)).add (a.mul (e.mul d))) b (b.mul (d.mul f))).symm).trans
      (congrArg (fun t : Int => t.mul (b.mul (d.mul f))) right.symm))

private theorem finite_add_assoc (a b c d e f : Int) :
    Eq ((((a.mul d).add (c.mul b)).mul f).add (e.mul (b.mul d)))
      ((a.mul (d.mul f)).add (((c.mul f).add (e.mul d)).mul b)) :=
  (congrArg (fun t : Int => t.add (e.mul (b.mul d))) (Int.add_mul (a.mul d) (c.mul b) f)).trans
    ((Int.add_assoc ((a.mul d).mul f) ((c.mul b).mul f) (e.mul (b.mul d))).trans
      (Eq.map₂ Int.add (Int.mul_assoc a d f)
        ((Eq.map₂ Int.add (Int.mul_right_comm c b f)
          ((congrArg e.mul (Int.mul_comm b d)).trans (Int.mul_assoc e d b).symm)).trans
          (Int.add_mul (c.mul f) (e.mul d) b).symm)))

/-- Compare all finite triples and propagate undefined in each coordinate. -/
private theorem on_triples
    (P : IntRatio → IntRatio → IntRatio → Prop)
    (left : ∀ y z, P undefined y z)
    (middle : ∀ a b z, P (fraction a b) undefined z)
    (right : ∀ a b c d, P (fraction a b) (fraction c d) undefined)
    (finite : ∀ a b c d e f, P (fraction a b) (fraction c d) (fraction e f))
    (x y z : IntRatio) : P x y z :=
  IntRatio.rec (motive := fun x => P x y z) (left y z)
    (fun a b => IntRatio.rec (motive := fun y => P (fraction a b) y z) (middle a b z)
      (fun c d => IntRatio.rec (motive := fun z => P (fraction a b) (fraction c d) z)
        (right a b c d) (finite a b c d) z) y) x

theorem add_assoc (x y z : IntRatio) : Equivalent ((x.add y).add z) (x.add (y.add z)) :=
  let P := fun (x y z : IntRatio) => Equivalent ((x.add y).add z) (x.add (y.add z))
  on_triples P
    (fun y z => IntRatio.rec (motive := fun y => P undefined y z) True.intro (fun _ _ => True.intro) y)
    (fun _ _ _ => True.intro)
    (fun _ _ _ _ => True.intro)
    (fun a b c d e f => Eq.map₂ Int.mul
      (finite_add_assoc a (denominator b) c (denominator d) e (denominator f))
      (Int.mul_assoc (denominator b) (denominator d) (denominator f)).symm) x y z

theorem mul_assoc (x y z : IntRatio) : Equivalent ((x.mul y).mul z) (x.mul (y.mul z)) :=
  let P := fun (x y z : IntRatio) => Equivalent ((x.mul y).mul z) (x.mul (y.mul z))
  on_triples P (fun _ _ => True.intro) (fun _ _ _ => True.intro) (fun _ _ _ _ => True.intro)
    (fun a b c d e f => Eq.map₂ Int.mul (Int.mul_assoc a c e)
      (Int.mul_assoc (denominator b) (denominator d) (denominator f)).symm) x y z

theorem mul_add (x y z : IntRatio) : Equivalent (x.mul (y.add z)) ((x.mul y).add (x.mul z)) :=
  let P := fun (x y z : IntRatio) => Equivalent (x.mul (y.add z)) ((x.mul y).add (x.mul z))
  on_triples P (fun _ _ => True.intro) (fun _ _ _ => True.intro) (fun _ _ _ _ => True.intro)
    (fun a b c d e f => mul_add_cross a (denominator b) c (denominator d) e (denominator f)) x y z

/-- Additive inverses for each finite ratio. -/
theorem add_neg (a : Int) (b : Nat) :
    Equivalent ((fraction a b).add (fraction a b).neg) (ofInt Int.zero) :=
  let d := denominator b
  have cancel := (congrArg ((a.mul d).add) (Int.neg_mul a d)).trans (Int.add_right_neg (a.mul d))
  (congrArg (fun t : Int => t.mul Int.one) cancel).trans
    ((Int.zero_mul Int.one).trans (Int.zero_mul (d.mul d)).symm)

theorem mul_inv_cancel (a : Int) (b : Nat) (ha : Not (Eq a Int.zero)) :
    Equivalent ((fraction a b).mul (fraction a b).inv) (ofInt Int.one) :=
  let P := fun a : Int => Not (Eq a Int.zero) →
    Equivalent ((fraction a b).mul (fraction a b).inv) (ofInt Int.one)
  (Int.rec (motive := P)
    (fun n => Nat.rec (motive := fun n => P (Int.ofNat n))
      (fun h => False.elim (h Eq.refl))
      (fun n _ _ =>
        let p := (denominator n).mul (denominator b)
        (Int.mul_one p).trans
          ((Int.mul_comm (denominator n) (denominator b)).trans
            (Int.one_mul ((denominator b).mul (denominator n))).symm)) n)
    (fun n _ =>
      let d := denominator b
      let v := denominator n
      (Int.mul_one (v.neg.mul d.neg)).trans
        ((Int.neg_mul_neg v d).trans ((Int.mul_comm v d).trans (Int.one_mul (d.mul v)).symm))) a) ha

theorem inv_congr {x y : IntRatio} (h : Equivalent x y) : Equivalent x.inv y.inv :=
  let P := fun (x y : IntRatio) => Equivalent x y → Equivalent x.inv y.inv
  (IntRatio.rec (motive := fun x => P x y)
    (IntRatio.rec (motive := fun y => P undefined y) (fun _ => True.intro) (fun _ _ h => False.elim h) y)
    (fun a b => IntRatio.rec (motive := fun y => P (fraction a b) y)
      (fun h => False.elim h)
      (fun c d (eq : Eq (a.mul (denominator d)) (c.mul (denominator b))) =>
        let x := fraction a b
        let y := fraction c d
        let one := ofInt Int.one
        (Int.eq_zero_or_ne_zero a).elim
          (fun ha =>
            have hc : Eq c Int.zero := Int.eq_of_mul_eq_mul_right (Int.ofNat_succ_ne_zero b)
              (eq.symm.trans ((congrArg (fun t : Int => t.mul (denominator d)) ha).trans
                ((Int.zero_mul (denominator d)).trans (Int.zero_mul (denominator b)).symm)))
            Eq.subst (fun a => Equivalent (fraction a b).inv (fraction c d).inv) ha.symm
              (Eq.subst (fun c => Equivalent (fraction Int.zero b).inv (fraction c d).inv)
                hc.symm True.intro))
          (fun ha =>
            have hc : Not (Eq c Int.zero) := fun hc => ha
              (Int.eq_of_mul_eq_mul_right (Int.ofNat_succ_ne_zero d)
                (eq.trans ((congrArg (fun t : Int => t.mul (denominator b)) hc).trans
                  ((Int.zero_mul (denominator b)).trans (Int.zero_mul (denominator d)).symm))))
            have withUnit := (mul_one x.inv).symm
            have insertInverse := mul_congr (equivalent_refl x.inv) (mul_inv_cancel c d hc).symm
            have reassociate := (mul_assoc x.inv y y.inv).symm
            have replace := mul_congr (mul_congr (equivalent_refl x.inv) (Equivalent.symm (x := x) (y := y) eq))
              (equivalent_refl y.inv)
            have cancel := mul_congr ((mul_comm x.inv x).trans (mul_inv_cancel a b ha))
              (equivalent_refl y.inv)
            have removeUnit := (mul_comm one y.inv).trans (mul_one y.inv)
            withUnit.trans (insertInverse.trans (reassociate.trans (replace.trans (cancel.trans removeUnit))))))
      y) x) h

/-- Multiplication combines the represented natural denominators, including zero. -/
theorem value_mul (a b : Int) (c d : Nat) :
    Eq ((value a c).mul (value b d)) (value (a.mul b) (c.mul d)) :=
  Nat.rec (motive := fun c => Eq ((value a c).mul (value b d)) (value (a.mul b) (c.mul d)))
    (congrArg (value (a.mul b)) (Nat.zero_mul d).symm)
    (fun c _ => Nat.rec (motive := fun d =>
      Eq ((value a c.succ).mul (value b d)) (value (a.mul b) (c.succ.mul d)))
      Eq.refl (fun _ _ => Eq.refl) d) c

theorem value_add_same (a b : Int) (d : Nat) :
    Equivalent ((value a d).add (value b d)) (value (a.add b) d) :=
  Nat.rec (motive := fun d =>
    Equivalent ((value a d).add (value b d)) (value (a.add b) d))
    True.intro (fun d _ =>
      let v := denominator d
      (congrArg (fun t : Int => t.mul v) (Int.add_mul a b v).symm).trans
        (Int.mul_assoc (a.add b) v v)) d

theorem value_self (n : Nat) (h : Not (Eq n Nat.zero)) :
    Equivalent (value (Int.ofNat n) n) (ofInt Int.one) :=
  (Nat.rec (motive := fun n => Not (Eq n Nat.zero) →
    Equivalent (value (Int.ofNat n) n) (ofInt Int.one))
    (fun h => False.elim (h Eq.refl))
    (fun d _ _ => (Int.mul_one (denominator d)).trans (Int.one_mul (denominator d)).symm) n) h

theorem value_zero (n : Nat) (h : Not (Eq n Nat.zero)) :
    Equivalent (value Int.zero n) (ofInt Int.zero) :=
  (Nat.rec (motive := fun n => Not (Eq n Nat.zero) → Equivalent (value Int.zero n) (ofInt Int.zero))
    (fun h => False.elim (h Eq.refl))
    (fun d _ _ => (Int.zero_mul Int.one).trans (Int.zero_mul (denominator d)).symm) n) h

private theorem le_of_equal_scalings (a b c d : Int) (k l : Nat)
    (ha : Eq (a.mul (denominator k)) (c.mul (denominator l)))
    (hb : Eq (b.mul (denominator k)) (d.mul (denominator l))) :
    Iff (a.le b) (c.le d) :=
  let first := Int.le_mul_ofNat_succ a b k
  let second := Int.le_mul_ofNat_succ c d l
  Iff.intro
    (fun h => second.mp (Eq.subst (fun t : Int => t.le (d.mul (denominator l))) ha
      (Eq.subst (Int.le (a.mul (denominator k))) hb (first.mpr h))))
    (fun h => first.mp (Eq.subst (fun t : Int => t.le (b.mul (denominator k))) ha.symm
      (Eq.subst (Int.le (c.mul (denominator l))) hb.symm (second.mpr h))))

private theorem le_congr_one {x y : IntRatio} (h : Equivalent x y) (z : IntRatio) :
    And (Iff (Le x z) (Le y z)) (Iff (Le z x) (Le z y)) :=
  let same := Iff.intro (fun h : False => h) (fun h : False => h)
  let P := fun x y z => Equivalent x y → And (Iff (Le x z) (Le y z)) (Iff (Le z x) (Le z y))
  on_triples P
    (fun y z => IntRatio.rec (motive := fun y => P undefined y z)
      (fun _ => IntRatio.rec (motive := fun z => And (Iff (Le undefined z) (Le undefined z))
        (Iff (Le z undefined) (Le z undefined))) (And.intro same same) (fun _ _ => And.intro same same) z)
      (fun _ _ h => False.elim h) y)
    (fun _ _ _ h => False.elim h)
    (fun _ _ _ _ _ => And.intro same same)
    (fun a b c d t u eq =>
      let B := denominator b
      let D := denominator d
      let U := denominator u
      have first : Eq ((a.mul U).mul D) ((c.mul U).mul B) :=
        (Int.mul_right_comm a U D).trans
          ((congrArg (fun n : Int => n.mul U) eq).trans (Int.mul_right_comm c B U))
      have second : Eq ((t.mul B).mul D) ((t.mul D).mul B) := Int.mul_right_comm t B D
      And.intro
        (le_of_equal_scalings (a.mul U) (t.mul B) (c.mul U) (t.mul D) d b first second)
        (le_of_equal_scalings (t.mul B) (a.mul U) (t.mul D) (c.mul U) d b second first))
    x y z h

theorem le_congr {x y z w : IntRatio} (h : Equivalent x y) (g : Equivalent z w) :
    Iff (Le x z) (Le y w) :=
  let left := (le_congr_one h z).left
  let right := (le_congr_one g y).right
  Iff.intro (fun p => right.mp (left.mp p)) (fun p => left.mpr (right.mpr p))

theorem lt_congr {x y z w : IntRatio} (h : Equivalent x y) (g : Equivalent z w) :
    Iff (Lt x z) (Lt y w) :=
  let le := le_congr h g
  Iff.intro
    (fun p => And.intro (le.mp p.left) (fun e => p.right (h.trans (e.trans g.symm))))
    (fun p => And.intro (le.mpr p.left) (fun e => p.right (h.symm.trans (e.trans g))))

theorem value_scale_of_ne_zero (a : Int) (d k : Nat) (hk : Not (Eq k Nat.zero)) :
    Equivalent (value (a.mul (Int.ofNat k)) (d.mul k)) (value a d) :=
  (Nat.rec (motive := fun k => Not (Eq k Nat.zero) →
    Equivalent (value (a.mul (Int.ofNat k)) (d.mul k)) (value a d))
    (fun h => False.elim (h Eq.refl)) (fun k _ _ => value_scale a d k) k) hk

theorem value_neg_self (n : Nat) (h : Not (Eq n Nat.zero)) :
    Equivalent (value (Int.ofNat n).neg n) (ofInt Int.one.neg) :=
  (Nat.rec (motive := fun n => Not (Eq n Nat.zero) →
    Equivalent (value (Int.ofNat n).neg n) (ofInt Int.one.neg))
    (fun h => False.elim (h Eq.refl))
    (fun d _ _ => (Int.mul_one (denominator d).neg).trans
      ((Int.neg_mul Int.one (denominator d)).trans
        (congrArg Int.neg (Int.one_mul (denominator d)))).symm) n) h

theorem value_cross_iff (a b : Int) (c d : Nat)
    (hc : Not (Eq c Nat.zero)) (hd : Not (Eq d Nat.zero)) :
    Iff (Equivalent (value a c) (value b d)) (Eq (a.mul (Int.ofNat d)) (b.mul (Int.ofNat c))) :=
  let P := fun c d => Not (Eq c Nat.zero) → Not (Eq d Nat.zero) →
    Iff (Equivalent (value a c) (value b d)) (Eq (a.mul (Int.ofNat d)) (b.mul (Int.ofNat c)))
  (Nat.rec (motive := fun c => P c d)
    (fun h _ => False.elim (h Eq.refl))
    (fun c _ => Nat.rec (motive := fun d => P c.succ d)
      (fun _ h => False.elim (h Eq.refl))
      (fun _ _ _ _ => Iff.intro (fun h => h) (fun h => h)) d) c) hc hd

end IntRatio
end Omega
