module
prelude
public import OmegaMath.Data.IntRatio

/-!
Omega original.

Finite rational coefficients and the cancellation laws for jets.
-/

noncomputable section

@[expose] public section

namespace Omega.IntRatio

def ofNat (n : Nat) : IntRatio := ofInt (Int.ofNat n)
def zero : IntRatio := ofInt Int.zero
def one : IntRatio := ofInt Int.one
def two : IntRatio := ofInt Int.two
def three : IntRatio := ofNat Nat.zero.succ.succ.succ

/-- The finite part of the extended rational representation. -/
def Finite (x : IntRatio) : Prop :=
  IntRatio.rec (motive := fun _ => Prop) False (fun _ _ => True) x

/-- A finite ratio with nonzero numerator. -/
def Unit (x : IntRatio) : Prop :=
  IntRatio.rec (motive := fun _ => Prop) False (fun a _ => Not (Eq a Int.zero)) x

theorem finite_ofNat (n : Nat) : Finite (ofNat n) := True.intro

theorem finite_add {x y : IntRatio} (hx : Finite x) (hy : Finite y) : Finite (x.add y) :=
  (IntRatio.rec (motive := fun x => Finite x → Finite (x.add y))
    (fun h => h)
    (fun a b _ => IntRatio.rec (motive := fun y => Finite y → Finite ((fraction a b).add y))
      (fun h => h) (fun _ _ _ => True.intro) y hy) x) hx

theorem finite_mul {x y : IntRatio} (hx : Finite x) (hy : Finite y) : Finite (x.mul y) :=
  (IntRatio.rec (motive := fun x => Finite x → Finite (x.mul y))
    (fun h => h)
    (fun a b _ => IntRatio.rec (motive := fun y => Finite y → Finite ((fraction a b).mul y))
      (fun h => h) (fun _ _ _ => True.intro) y hy) x) hx

theorem finite_neg {x : IntRatio} (hx : Finite x) : Finite x.neg :=
  (IntRatio.rec (motive := fun x => Finite x → Finite x.neg)
    (fun h => h) (fun _ _ _ => True.intro) x) hx

theorem unit_ofNat_succ (k : Nat) : Unit (ofNat k.succ) := Int.ofNat_succ_ne_zero k

theorem unit_finite {x : IntRatio} (hx : Unit x) : Finite x :=
  (IntRatio.rec (motive := fun x => Unit x → Finite x)
    (fun h => h) (fun _ _ _ => True.intro) x) hx

theorem finite_inv {x : IntRatio} (hx : Unit x) : Finite x.inv :=
  (IntRatio.rec (motive := fun x => Unit x → Finite x.inv) (fun h => h)
    (fun a b => Int.rec (motive := fun a => Unit (fraction a b) → Finite (fraction a b).inv)
      (fun n => Nat.rec (motive := fun n => Unit (fraction (Int.ofNat n) b) →
        Finite (fraction (Int.ofNat n) b).inv)
        (fun h => h Eq.refl) (fun _ _ _ => True.intro) n)
      (fun _ _ => True.intro) a) x) hx

theorem mul_inv {x : IntRatio} (hx : Unit x) : Equivalent (x.mul x.inv) one :=
  (IntRatio.rec (motive := fun x => Unit x → Equivalent (x.mul x.inv) one)
    (fun h => h) (fun a b h => mul_inv_cancel a b h) x) hx

theorem mul_cancel_left {a x y : IntRatio} (ha : Unit a)
    (h : Equivalent (a.mul x) (a.mul y)) : Equivalent x y :=
  have strip : ∀ t : IntRatio, Equivalent (a.inv.mul (a.mul t)) t := fun t =>
    (mul_assoc a.inv a t).symm.trans
      ((mul_congr ((mul_comm a.inv a).trans (mul_inv ha)) (equivalent_refl t)).trans
        ((mul_comm one t).trans (mul_one t)))
  (strip x).symm.trans ((mul_congr (equivalent_refl a.inv) h).trans (strip y))

theorem zero_add (x : IntRatio) : Equivalent (zero.add x) x :=
  (add_comm zero x).trans (add_zero x)

theorem one_mul (x : IntRatio) : Equivalent (one.mul x) x :=
  (mul_comm one x).trans (mul_one x)

theorem mul_zero {x : IntRatio} (hx : Finite x) : Equivalent (x.mul zero) zero :=
  (IntRatio.rec (motive := fun x => Finite x → Equivalent (x.mul zero) zero)
    (fun h => h) (fun a b _ =>
      (congrArg (fun t : Int => t.mul Int.one) (Int.mul_zero a)).trans
        ((Int.mul_zero Int.zero).trans (Int.zero_mul (denominator (mulDenPred b Nat.zero))).symm)) x) hx

theorem zero_mul {x : IntRatio} (hx : Finite x) : Equivalent (zero.mul x) zero :=
  (mul_comm zero x).trans (mul_zero hx)

theorem add_right_neg {x : IntRatio} (hx : Finite x) : Equivalent (x.add x.neg) zero :=
  (IntRatio.rec (motive := fun x => Finite x → Equivalent (x.add x.neg) zero)
    (fun h => h) (fun a b _ => add_neg a b) x) hx

theorem add_left_neg {x : IntRatio} (hx : Finite x) : Equivalent (x.neg.add x) zero :=
  (add_comm x.neg x).trans (add_right_neg hx)

theorem neg_neg (x : IntRatio) : Equivalent x.neg.neg x :=
  IntRatio.rec (motive := fun x => Equivalent x.neg.neg x) True.intro
    (fun a b => congrArg (fun t : Int => t.mul (denominator b)) (Int.neg_neg a)) x

theorem neg_add (x y : IntRatio) : Equivalent (x.add y).neg (x.neg.add y.neg) :=
  IntRatio.rec (motive := fun x => Equivalent (x.add y).neg (x.neg.add y.neg)) True.intro
    (fun a b => IntRatio.rec (motive := fun y =>
      Equivalent ((fraction a b).add y).neg ((fraction a b).neg.add y.neg))
      True.intro (fun c d =>
        congrArg (fun t : Int => t.mul (denominator (mulDenPred b d)))
          (Int.neg_add.trans (Eq.map₂ Int.add (Int.neg_mul a (denominator d)).symm
            (Int.neg_mul c (denominator b)).symm))) y) x

theorem mul_neg (x y : IntRatio) : Equivalent (x.mul y.neg) (x.mul y).neg :=
  IntRatio.rec (motive := fun x => Equivalent (x.mul y.neg) (x.mul y).neg) True.intro
    (fun a b => IntRatio.rec (motive := fun y =>
      Equivalent ((fraction a b).mul y.neg) ((fraction a b).mul y).neg)
      True.intro (fun c d => congrArg (fun t : Int => t.mul (denominator (mulDenPred b d)))
        (Int.mul_neg a c)) y) x

theorem neg_mul (x y : IntRatio) : Equivalent (x.neg.mul y) (x.mul y).neg :=
  (mul_comm x.neg y).trans ((mul_neg y x).trans (neg_congr (mul_comm y x)))

theorem add_mul (x y z : IntRatio) : Equivalent ((x.add y).mul z) ((x.mul z).add (y.mul z)) :=
  (mul_comm (x.add y) z).trans ((mul_add z x y).trans (add_congr (mul_comm z x) (mul_comm z y)))

theorem add_right_comm (x y z : IntRatio) :
    Equivalent ((x.add y).add z) ((x.add z).add y) :=
  (add_assoc x y z).trans
    ((add_congr (equivalent_refl x) (add_comm y z)).trans (add_assoc x z y).symm)

theorem add_add_add_comm (w x y z : IntRatio) :
    Equivalent ((w.add x).add (y.add z)) ((w.add y).add (x.add z)) :=
  (add_assoc (w.add x) y z).symm.trans
    ((add_congr (add_right_comm w x y) (equivalent_refl z)).trans (add_assoc (w.add y) x z))

theorem mul_right_comm (x y z : IntRatio) :
    Equivalent ((x.mul y).mul z) ((x.mul z).mul y) :=
  (mul_assoc x y z).trans
    ((mul_congr (equivalent_refl x) (mul_comm y z)).trans (mul_assoc x z y).symm)

theorem mul_mul_mul_comm (w x y z : IntRatio) :
    Equivalent ((w.mul x).mul (y.mul z)) ((w.mul y).mul (x.mul z)) :=
  (mul_assoc (w.mul x) y z).symm.trans
    ((mul_congr (mul_right_comm w x y) (equivalent_refl z)).trans (mul_assoc (w.mul y) x z))

theorem ofNat_add (m n : Nat) : Eq ((ofNat m).add (ofNat n)) (ofNat (m.add n)) :=
  congrArg (fun t : Int => fraction t Nat.zero)
    (Eq.map₂ Int.add (Int.mul_one (Int.ofNat m)) (Int.mul_one (Int.ofNat n)))

theorem ofNat_mul (m n : Nat) : Eq ((ofNat m).mul (ofNat n)) (ofNat (m.mul n)) :=
  Eq.refl

theorem two_mul (x : IntRatio) : Equivalent (two.mul x) (x.add x) :=
  (add_mul one one x).trans (add_congr (one_mul x) (one_mul x))


theorem unit_mul {x y : IntRatio} (hx : Unit x) (hy : Unit y) : Unit (x.mul y) :=
  (IntRatio.rec (motive := fun x => Unit x → Unit (x.mul y))
    (fun h => h)
    (fun a b ha => IntRatio.rec (motive := fun y => Unit y → Unit ((fraction a b).mul y))
      (fun h => h) (fun c _ hc h => ha (Int.eq_of_mul_eq_mul_right hc (h.trans (Int.zero_mul c).symm)))
      y hy) x) hx

theorem inv_mul {x y : IntRatio} (hx : Unit x) (hy : Unit y) :
    Equivalent (x.mul y).inv (x.inv.mul y.inv) :=
  mul_cancel_left (unit_mul hx hy)
    ((mul_inv (unit_mul hx hy)).trans
      (((mul_mul_mul_comm x y x.inv y.inv).trans
        ((mul_congr (mul_inv hx) (mul_inv hy)).trans (mul_one one))).symm))

theorem sub_mul (x y z : IntRatio) :
    Equivalent ((x.sub y).mul z) ((x.mul z).sub (y.mul z)) :=
  (add_mul x y.neg z).trans (add_congr (equivalent_refl (x.mul z)) (neg_mul y z))

theorem mul_sub (x y z : IntRatio) :
    Equivalent (x.mul (y.sub z)) ((x.mul y).sub (x.mul z)) :=
  (mul_add x y z.neg).trans (add_congr (equivalent_refl (x.mul y)) (mul_neg x z))

theorem sub_self {x : IntRatio} (hx : Finite x) : Equivalent (x.sub x) zero :=
  add_right_neg hx

theorem add_sub_cancel {x y : IntRatio} (hy : Finite y) : Equivalent ((x.add y).sub y) x :=
  (add_assoc x y y.neg).trans
    ((add_congr (equivalent_refl x) (add_right_neg hy)).trans (add_zero x))

theorem unit_one_add_sq {x : IntRatio} (hx : Finite x) : Unit (one.add (x.mul x)) :=
  (IntRatio.rec (motive := fun x => Finite x → Unit (one.add (x.mul x)))
    (fun h => False.elim h) (fun a b _ h =>
      let d := denominator b
      have numer : Eq ((Int.one.mul (denominator (mulDenPred b b))).add ((a.mul a).mul Int.one))
          ((d.mul d).add (a.mul a)) :=
        Eq.map₂ Int.add ((Int.one_mul (denominator (mulDenPred b b))).trans (denominator_mul b b))
          (Int.mul_one (a.mul a))
      Int.ofNat_succ_ne_zero b ((Int.sum_of_two_squares_eq_zero d a).mp (numer.symm.trans h)).left)
    x) hx

end Omega.IntRatio
