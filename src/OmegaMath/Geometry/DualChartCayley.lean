/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude
import all OmegaInit.Data.Int.Basic
public import OmegaMath.Geometry.Cayley3D

/-!
Omega original.

Dual modified Rodrigues charts for the product of two stereographic quaternion lifts.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.DualChartCayley

open Quaternion.Polynomial

/-- The stereographic lift of a rational vector to a signed unit quaternion. -/
def lift (u : RatVec3) : PythSpinor :=
  let d := Int.ofNat u.den
  let sq := fun (n : Int) => n.natAbs.mul n.natAbs
  let s := (sq u.num.x).add ((sq u.num.y).add (sq u.num.z))
  let k := IntRatio.mulDenPred u.denPred u.denPred
  have squareDen : Eq (sq d) k.succ :=
    (Nat.mul_succ u.den u.denPred).trans (Nat.add_succ (u.den.mul u.denPred) u.denPred)
  have radius : Eq (PythSpinor.liftRadius d u.num.x u.num.y u.num.z) (k.add s).succ :=
    (congrArg (fun n : Nat => n.add s) squareDen).trans (Nat.succ_add k s)
  PythSpinor.ofNumerator (PythSpinor.liftNum d u.num.x u.num.y u.num.z) (k.add s)
    ((PythSpinor.lift_normSq d u.num.x u.num.y u.num.z).trans
      (congrArg (fun n : Nat => n.mul n) radius))

def product (u v : RatVec3) : PythSpinor := (lift u).mul (lift v)

/-- The normalized denominator `(r + w) / (2r)` of the positive chart. -/
def denomPlus (u v : RatVec3) : IntRatio :=
  let p := product u v
  IntRatio.fraction ((Int.ofNat p.radius).add p.num.w)
    (IntRatio.mulDenPred p.radiusPred Nat.zero.succ)

/-- The normalized denominator `(r - w) / (2r)` of the negative chart. -/
def denomMinus (u v : RatVec3) : IntRatio :=
  let p := product u v
  IntRatio.fraction ((Int.ofNat p.radius).sub p.num.w)
    (IntRatio.mulDenPred p.radiusPred Nat.zero.succ)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
theorem dual_chart_denom_sum_one (u v : RatVec3) :
    IntRatio.Equivalent ((denomPlus u v).add (denomMinus u v)) (IntRatio.ofInt Int.one) :=
  let p := product u v
  let r := Int.ofNat p.radius
  let w := p.num.w
  let k := IntRatio.mulDenPred p.radiusPred Nat.zero.succ
  let R := Expr.var Nat.zero
  let W := Expr.var Nat.zero.succ
  have sum : Eq ((r.add w).add (r.sub w)) (Int.ofNat k.succ) :=
    ((R.add W).add (R.sub W)).sound (R.mul Expr.one.double) (.cons r (.cons w .nil)) rfl
  (IntRatio.value_add_same (r.add w) (r.sub w) k.succ).trans
    (Eq.subst (motive := fun n => IntRatio.Equivalent (IntRatio.fraction n k) (IntRatio.ofInt Int.one))
      sum.symm (IntRatio.value_self k.succ (Nat.succ_ne_zero k)))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem half_le_add (k a : Nat) :
    IntRatio.Le (IntRatio.fraction Int.one Nat.zero.succ)
      (IntRatio.fraction ((IntRatio.denominator k).add (Int.ofNat a))
        (IntRatio.mulDenPred k Nat.zero.succ)) :=
  let r := IntRatio.denominator k
  let R := Expr.var Nat.zero
  let A := Expr.var Nat.zero.succ
  let two := Expr.one.double
  have gap : Eq (((r.add (Int.ofNat a)).mul Int.two).sub (Int.one.mul (r.mul Int.two)))
      ((Int.ofNat a).mul Int.two) :=
    (((R.add A).mul two).sub (Expr.one.mul (R.mul two))).sound
      (A.mul two) (.cons r (.cons (Int.ofNat a) .nil)) rfl
  Eq.subst (motive := Int.NonNeg) gap.symm (Int.NonNeg.mk (a.mul Nat.zero.succ.succ))

theorem dual_chart_denom_ge_half (u v : RatVec3) :
    let half := IntRatio.fraction Int.one Nat.zero.succ
    Or (IntRatio.Le half (denomPlus u v)) (IntRatio.Le half (denomMinus u v)) :=
  let k := (product u v).radiusPred
  let r := IntRatio.denominator k
  let n := IntRatio.mulDenPred k Nat.zero.succ
  let half := IntRatio.fraction Int.one Nat.zero.succ
  Int.rec (motive := fun w =>
    Or (IntRatio.Le half (IntRatio.fraction (r.add w) n))
      (IntRatio.Le half (IntRatio.fraction (r.sub w) n)))
    (fun a => Or.inl (half_le_add k a))
    (fun a => Or.inr (half_le_add k a.succ)) (product u v).num.w

/-- Use the positive chart for a nonnegative scalar and the negative chart otherwise. -/
def orientNumerator (w : Int) (v : Vec3) : Vec3 :=
  Int.rec (fun _ => v) (fun _ => ⟨v.x.neg, v.y.neg, v.z.neg⟩) w

/-- The imaginary coordinates divided by `r + |w|`, with their sign reversed when `w < 0`.
At `w = 0` the positive chart is selected. -/
def output (u v : RatVec3) : RatVec3 :=
  let p := product u v
  ⟨orientNumerator p.num.w (Vec3.imaginary p.num), p.radiusPred.add p.num.w.natAbs⟩

theorem output_den (u v : RatVec3) :
    Eq (output u v).den ((product u v).radius.add (product u v).num.w.natAbs) :=
  (Nat.succ_add (product u v).radiusPred (product u v).num.w.natAbs).symm

private theorem orient_dot (w : Int) (v : Vec3) :
    Eq ((orientNumerator w v).dot3 (orientNumerator w v)) (v.dot3 v) :=
  Int.rec (motive := fun w => Eq ((orientNumerator w v).dot3 (orientNumerator w v)) (v.dot3 v))
    (fun _ => rfl)
    (fun _ => Eq.map₂ Int.add (Int.neg_mul_neg v.x v.x)
      (Eq.map₂ Int.add (Int.neg_mul_neg v.y v.y) (Int.neg_mul_neg v.z v.z))) w

private theorem unit_norm (p : PythSpinor) :
    Eq ((Int.square p.num.w).add ((Vec3.imaginary p.num).dot3 (Vec3.imaginary p.num)))
      (Int.square (Int.ofNat p.radius)) :=
  (Int.add_assoc (Int.square p.num.w) (Int.square p.num.x)
    ((Int.square p.num.y).add (Int.square p.num.z))).symm.trans
    (p.num.normSq_cast.symm.trans (congrArg Int.ofNat p.normSq_eq))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem ball_gap (r a s : Int) :
    Eq ((Int.square (r.add a)).sub s)
      (((Int.square r).sub ((Int.square a).add s)).add ((Int.two.mul a).mul (r.add a))) :=
  let R := Expr.var Nat.zero
  let A := Expr.var Nat.zero.succ
  let S := Expr.var Nat.zero.succ.succ
  ((R.add A).sq.sub S).sound
    ((R.sq.sub (A.sq.add S)).add ((Expr.one.double.mul A).mul (R.add A)))
    (.cons r (.cons a (.cons s .nil))) rfl

/-- The selected chart sends the product into the closed unit ball. -/
theorem dual_chart_ball_containment (u v : RatVec3) :
    IntRatio.Le ((output u v).dot3 (output u v)) (IntRatio.ofInt Int.one) :=
  let p := product u v
  let t := output u v
  let r := Int.ofNat p.radius
  let a := Int.ofNat p.num.w.natAbs
  let imaginary := Vec3.imaginary p.num
  let s := imaginary.dot3 imaginary
  let d := Int.square (Int.ofNat t.den)
  let n := t.num.dot3 t.num
  let gap := (Int.two.mul a).mul (r.add a)
  have norm : Eq ((Int.square a).add s) (Int.square r) :=
    (congrArg (fun x : Int => x.add s) Int.natAbs_mul_self).trans (unit_norm p)
  have cancel : Eq ((Int.square r).sub ((Int.square a).add s)) Int.zero :=
    (congrArg ((Int.square r).sub) norm).trans (Int.add_right_neg (Int.square r))
  have diff : Eq ((Int.one.mul d).sub (n.mul Int.one)) gap :=
    (Eq.map₂ Int.sub (Int.one_mul d) (Int.mul_one n)).trans
      ((Eq.map₂ Int.sub (congrArg (fun k => Int.square (Int.ofNat k)) (output_den u v))
        (orient_dot p.num.w imaginary)).trans
        ((ball_gap r a s).trans
          ((congrArg (fun x : Int => x.add gap) cancel).trans (Int.zero_add gap))))
  have nonneg := Eq.subst (motive := Int.NonNeg) diff.symm
    (Int.NonNeg.mk ((Nat.zero.succ.succ.mul p.num.w.natAbs).mul (p.radius.add p.num.w.natAbs)))
  have cross := Eq.subst (motive := fun z => Int.NonNeg ((Int.one.mul z).sub (n.mul Int.one)))
    (IntRatio.denominator_mul t.denPred t.denPred).symm nonneg
  Eq.subst (motive := fun z => IntRatio.Le (IntRatio.value n z) (IntRatio.ofInt Int.one))
    (IntRatio.nat_denominator_mul t.denPred t.denPred).symm cross

/-- The expanded MRP numerator before chart orientation.
For integer numerators `x, y` and positive denominators `d, e`, it is
`d(e² - y·y)x + e(d² - x·x)y + 2de(x × y)`. -/
def mrpNumerator (u v : RatVec3) : Vec3 :=
  let x := u.num
  let y := v.num
  let d := Int.ofNat u.den
  let e := Int.ofNat v.den
  let a := (Int.square d).sub (x.dot3 x)
  let b := (Int.square e).sub (y.dot3 y)
  let component := fun (xi yi cross : Int) =>
    ((d.mul b).mul xi).add (((e.mul a).mul yi).add (((Int.two.mul d).mul e).mul cross))
  ⟨component x.x y.x ((x.y.mul y.z).sub (x.z.mul y.y)),
   component x.y y.y ((x.z.mul y.x).sub (x.x.mul y.z)),
   component x.z y.z ((x.x.mul y.y).sub (x.y.mul y.x))⟩

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul in
theorem mrp_product_imaginary (u v : RatVec3) :
    Eq (Vec3.imaginary (product u v).num) (Vec3.scale Int.two (mrpNumerator u v)) :=
  let x := u.num
  let y := v.num
  let d := Int.ofNat u.den
  let e := Int.ofNat v.den
  let a := (Int.square d).sub (x.dot3 x)
  let b := (Int.square e).sub (y.dot3 y)
  let i := Nat.zero.succ.succ.succ.succ
  let first := Coordinates.variables Nat.zero
  let second := Coordinates.variables i
  let D := Expr.var i.succ.succ.succ.succ
  let E := Expr.var i.succ.succ.succ.succ.succ
  let two := Expr.one.double
  let liftFirst := Coordinates.mk first.w
    ((two.mul D).mul first.x) ((two.mul D).mul first.y) ((two.mul D).mul first.z)
  let liftSecond := Coordinates.mk second.w
    ((two.mul E).mul second.x) ((two.mul E).mul second.y) ((two.mul E).mul second.z)
  let multiplied := liftFirst.mul liftSecond
  let component := fun (xi yi cross : Expr) =>
    two.mul (((D.mul second.w).mul xi).add
      (((E.mul first.w).mul yi).add (((two.mul D).mul E).mul cross)))
  let values := Values.cons a (.cons x.x (.cons x.y (.cons x.z
    (.cons b (.cons y.x (.cons y.y (.cons y.z (.cons d (.cons e .nil)))))))))
  Vec3.ext
    (multiplied.x.sound (component first.x second.x
      ((first.y.mul second.z).sub (first.z.mul second.y))) values rfl)
    (multiplied.y.sound (component first.y second.y
      ((first.z.mul second.x).sub (first.x.mul second.z))) values rfl)
    (multiplied.z.sound (component first.z second.z
      ((first.x.mul second.y).sub (first.y.mul second.x))) values rfl)

theorem mrp_output_num (u v : RatVec3) :
    Eq (output u v).num
      (orientNumerator (product u v).num.w (Vec3.scale Int.two (mrpNumerator u v))) :=
  congrArg (orientNumerator (product u v).num.w) (mrp_product_imaginary u v)

private theorem lift_radius_cast (u : RatVec3) :
    Eq (Int.ofNat (lift u).radius) ((Int.ofNat u.den).square.add (u.num.dot3 u.num)) :=
  (congrArg Int.ofNat
    (Nat.succ_add (IntRatio.mulDenPred u.denPred u.denPred) _).symm).trans
    (Eq.map₂ Int.add (IntRatio.denominator_mul u.denPred u.denPred)
      (Eq.map₂ Int.add (Int.natAbs_mul_self (a := u.num.x))
        (Eq.map₂ Int.add (Int.natAbs_mul_self (a := u.num.y))
          (Int.natAbs_mul_self (a := u.num.z)))))

/-- The primary MRP numerator after clearing the input denominators. -/
def mrpPlusNum (u v : RatVec3) : Int :=
  let d := Int.ofNat u.den
  let e := Int.ofNat v.den
  ((d.square.mul e.square).add ((u.num.dot3 u.num).mul (v.num.dot3 v.num))).sub
    (((Int.two.mul d).mul e).mul (u.num.dot3 v.num))

/-- The shadow MRP numerator after clearing the input denominators. -/
def mrpMinusNum (u v : RatVec3) : Int :=
  let d := Int.ofNat u.den
  let e := Int.ofNat v.den
  (((u.num.dot3 u.num).mul e.square).add (d.square.mul (v.num.dot3 v.num))).add
    (((Int.two.mul d).mul e).mul (u.num.dot3 v.num))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem product_scalar (u v : RatVec3) :
    let d := Int.ofNat u.den
    let e := Int.ofNat v.den
    Eq (product u v).num.w
      (((d.square.sub (u.num.dot3 u.num)).mul (e.square.sub (v.num.dot3 v.num))).sub
        ((((Int.two.mul Int.two).mul d).mul e).mul (u.num.dot3 v.num))) :=
  let i := Nat.zero
  let j := i.succ.succ.succ.succ
  let U := Coordinates.variables i
  let V := Coordinates.variables j
  let d := Expr.var j.succ.succ.succ.succ
  let e := Expr.var j.succ.succ.succ.succ.succ
  let two := Expr.one.double
  let a := U.w
  let b := V.w
  let x := u.num
  let y := v.num
  let liftU := Coordinates.mk a
    ((two.mul d).mul U.x) ((two.mul d).mul U.y) ((two.mul d).mul U.z)
  let liftV := Coordinates.mk b
    ((two.mul e).mul V.x) ((two.mul e).mul V.y) ((two.mul e).mul V.z)
  let dot := (U.x.mul V.x).add ((U.y.mul V.y).add (U.z.mul V.z))
  let du := Int.ofNat u.den
  let dv := Int.ofNat v.den
  let values := Values.cons (du.square.sub (x.dot3 x)) (.cons x.x (.cons x.y (.cons x.z
    (.cons (dv.square.sub (y.dot3 y)) (.cons y.x (.cons y.y (.cons y.z
      (.cons du (.cons dv .nil)))))))))
  (liftU.mul liftV).w.sound ((a.mul b).sub ((((two.mul two).mul d).mul e).mul dot)) values rfl

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
/-- The normalized quaternion denominators agree with the explicit MRP formulas. -/
theorem dual_chart_mrp_denominators (u v : RatVec3) :
    let r := (product u v).radiusPred
    And (IntRatio.Equivalent (denomPlus u v) (.fraction (mrpPlusNum u v) r))
      (IntRatio.Equivalent (denomMinus u v) (.fraction (mrpMinusNum u v) r)) :=
  let p := product u v
  let r := Int.ofNat p.radius
  let d := Int.ofNat u.den
  let e := Int.ofNat v.den
  let x := u.num.dot3 u.num
  let y := v.num.dot3 v.num
  let z := u.num.dot3 v.num
  have hr : Eq r ((d.square.add x).mul (e.square.add y)) :=
    (IntRatio.denominator_mul (lift u).radiusPred (lift v).radiusPred).trans
      (Eq.map₂ Int.mul (lift_radius_cast u) (lift_radius_cast v))
  let D := Expr.var Nat.zero
  let E := Expr.var Nat.zero.succ
  let X := Expr.var Nat.zero.succ.succ
  let Y := Expr.var Nat.zero.succ.succ.succ
  let Z := Expr.var Nat.zero.succ.succ.succ.succ
  let two := Expr.one.double
  let scaledDot := ((two.mul D).mul E).mul Z
  let productRadius := (D.sq.add X).mul (E.sq.add Y)
  let scalar := ((D.sq.sub X).mul (E.sq.sub Y)).sub ((((two.mul two).mul D).mul E).mul Z)
  let mrpPlus := ((D.sq.mul E.sq).add (X.mul Y)).sub scaledDot
  let mrpMinus := ((X.mul E.sq).add (D.sq.mul Y)).add scaledDot
  let values := Values.cons d (.cons e (.cons x (.cons y (.cons z .nil))))
  have hp : Eq (r.add p.num.w) ((mrpPlusNum u v).mul Int.two) :=
    (Eq.map₂ Int.add hr (product_scalar u v)).trans
      ((productRadius.add scalar).sound (mrpPlus.mul two) values rfl)
  have hm : Eq (r.sub p.num.w) ((mrpMinusNum u v).mul Int.two) :=
    (Eq.map₂ Int.sub hr (product_scalar u v)).trans
      ((productRadius.sub scalar).sound (mrpMinus.mul two) values rfl)
  have cancel : ∀ (a b : Int), Eq a (b.mul Int.two) →
      IntRatio.Equivalent (.fraction a (IntRatio.mulDenPred p.radiusPred Nat.one))
        (.fraction b p.radiusPred) :=
    fun _a b h => Eq.subst (motive := fun n => IntRatio.Equivalent
      (.fraction n (IntRatio.mulDenPred p.radiusPred Nat.one)) (.fraction b p.radiusPred))
      h.symm (IntRatio.value_scale b p.radius Nat.one)
  And.intro (cancel _ _ hp) (cancel _ _ hm)

end Omega.Geometry.DualChartCayley
