module
prelude
public import OmegaMath.Calculus.Jet2.Fidelity

/-!
Omega original.

The fidelity secant discrepancy is a rational identity in the base point and step.
-/

noncomputable section

@[expose] public section

namespace Omega.Jet2

private theorem mul_inv_right (x : IntRatio) {y : IntRatio} (hy : y.Unit) :
    IntRatio.Equivalent ((x.mul y).mul y.inv) x :=
  (IntRatio.mul_assoc x y y.inv).trans
    ((IntRatio.mul_congr (IntRatio.equivalent_refl x) (IntRatio.mul_inv hy)).trans (IntRatio.mul_one x))

private theorem mul_div_cancel (x : IntRatio) {y : IntRatio} (hy : y.Unit) :
    IntRatio.Equivalent (y.mul (x.mul y.inv)) x :=
  (IntRatio.mul_assoc y x y.inv).symm.trans
    ((IntRatio.mul_congr (IntRatio.mul_comm y x) (IntRatio.equivalent_refl y.inv)).trans (mul_inv_right x hy))

private theorem den_increment (x h : IntRatio) :
    IntRatio.Equivalent (fidelityDen (x.add h))
      ((fidelityDen x).add (h.mul ((IntRatio.two.mul x).add h))) :=
  let xx := x.mul x
  let hx := h.mul x
  let hh := h.mul h
  have expand := (IntRatio.mul_add (x.add h) x h).trans (IntRatio.add_congr (IntRatio.add_mul x h x) (IntRatio.add_mul x h h))
  have regroup := (IntRatio.add_congr (IntRatio.equivalent_refl (xx.add hx))
      (IntRatio.add_congr (IntRatio.mul_comm x h) (IntRatio.equivalent_refl hh))).trans
    ((IntRatio.add_assoc xx hx (hx.add hh)).trans
      (IntRatio.add_congr (IntRatio.equivalent_refl xx) (IntRatio.add_assoc hx hx hh).symm))
  have factor := (IntRatio.mul_add h (IntRatio.two.mul x) h).trans
    (IntRatio.add_congr ((IntRatio.mul_congr (IntRatio.equivalent_refl h) (IntRatio.two_mul x)).trans (IntRatio.mul_add h x x))
      (IntRatio.equivalent_refl hh))
  (IntRatio.add_congr (IntRatio.equivalent_refl IntRatio.one) (expand.trans (regroup.trans
      (IntRatio.add_congr (IntRatio.equivalent_refl xx) factor.symm)))).trans
    (IntRatio.add_assoc IntRatio.one xx (h.mul ((IntRatio.two.mul x).add h))).symm

private theorem sub_common {a : IntRatio} (ha : a.Finite) (b c : IntRatio) :
    IntRatio.Equivalent ((a.add b).sub (a.add c)) (b.sub c) :=
  (IntRatio.add_congr (IntRatio.equivalent_refl (a.add b)) (IntRatio.neg_add a c)).trans
    ((IntRatio.add_add_add_comm a b a.neg c.neg).trans
      ((IntRatio.add_congr (IntRatio.add_right_neg ha) (IntRatio.equivalent_refl (b.sub c))).trans
        (IntRatio.zero_add (b.sub c))))

private theorem step_numerator (x h : IntRatio) (hx : x.Finite) :
    IntRatio.Equivalent
      (((IntRatio.two.mul x).mul ((IntRatio.two.mul x).add h)).sub (fidelityDen x))
      (((IntRatio.three.mul (x.mul x)).add ((IntRatio.two.mul x).mul h)).sub IntRatio.one) :=
  let t := x.mul x
  let b := IntRatio.two.mul x
  let u := b.mul h
  let a := fidelityDen x
  have shift := (IntRatio.add_right_comm (b.mul b) u a.neg).trans
    (IntRatio.add_congr (b_sq_sub_den x hx) (IntRatio.equivalent_refl u))
  (IntRatio.sub_congr (IntRatio.mul_add b b h) (IntRatio.equivalent_refl a)).trans
    (shift.trans (IntRatio.add_right_comm (IntRatio.three.mul t) IntRatio.one.neg u))

/-- The difference of the finite secant slope and the linear jet coefficient. -/
theorem kappa_secant_discrepancy (x h : IntRatio) (hx : x.Finite) (hu : h.Unit) :
    IntRatio.Equivalent ((((kappa (x.add h)).sub (kappa x)).mul h.inv).sub (kappaJetAt x).first)
      ((h.mul (((IntRatio.three.mul (x.mul x)).add ((IntRatio.two.mul x).mul h)).sub IntRatio.one)).mul
        ((((fidelityDen x).mul (fidelityDen x)).mul (fidelityDen (x.add h))).inv)) :=
  let a := fidelityDen x
  let b := fidelityDen (x.add h)
  let aSq := a.mul a
  let den := aSq.mul b
  let c := IntRatio.two.mul x
  let d := c.add h
  let numerator := h.mul (((IntRatio.three.mul (x.mul x)).add (c.mul h)).sub IntRatio.one)
  have ua := IntRatio.unit_one_add_sq hx
  have ub := IntRatio.unit_one_add_sq (IntRatio.finite_add hx (IntRatio.unit_finite hu))
  have uSq := IntRatio.unit_mul ua ua
  have uDen := IntRatio.unit_mul uSq ub
  have fa := IntRatio.finite_add (x := IntRatio.one) True.intro (IntRatio.finite_mul hx hx)
  have step := den_increment x h
  have denA := (IntRatio.mul_congr (IntRatio.mul_right_comm a a b) (IntRatio.equivalent_refl a.inv)).trans
    (mul_inv_right (a.mul b) ua)
  have denB := mul_inv_right aSq ub
  have difference := (IntRatio.mul_sub den b.inv a.inv).trans (IntRatio.sub_congr denB denA)
  have ab := (IntRatio.mul_congr (IntRatio.equivalent_refl a) step).trans (IntRatio.mul_add a a (h.mul d))
  have cancelSq := (IntRatio.sub_congr (IntRatio.equivalent_refl aSq) ab).trans
    ((sub_add aSq aSq (a.mul (h.mul d))).trans
      ((IntRatio.sub_congr (IntRatio.sub_self (IntRatio.finite_mul fa fa))
          (IntRatio.equivalent_refl (a.mul (h.mul d)))).trans
        (IntRatio.zero_add (a.mul (h.mul d)).neg)))
  have shrink := (IntRatio.mul_congr (IntRatio.mul_assoc a h d).symm (IntRatio.equivalent_refl h.inv)).trans
    ((IntRatio.mul_congr (IntRatio.mul_right_comm a h d) (IntRatio.equivalent_refl h.inv)).trans
      (mul_inv_right (a.mul d) hu))
  have scaledSlope := (IntRatio.mul_assoc den (b.inv.sub a.inv) h.inv).symm.trans
    ((IntRatio.mul_congr (difference.trans cancelSq) (IntRatio.equivalent_refl h.inv)).trans
      ((IntRatio.neg_mul (a.mul (h.mul d)) h.inv).trans (IntRatio.neg_congr shrink)))
  have scaledLinear := (IntRatio.mul_congr (IntRatio.equivalent_refl den) (IntRatio.mul_comm c.neg aSq.inv)).trans
    ((IntRatio.mul_mul_mul_comm aSq b aSq.inv c.neg).trans
      ((IntRatio.mul_congr (IntRatio.mul_inv uSq) (IntRatio.equivalent_refl (b.mul c.neg))).trans
        ((IntRatio.one_mul (b.mul c.neg)).trans (IntRatio.mul_neg b c))))
  have reorder := (IntRatio.add_congr (IntRatio.equivalent_refl (a.mul d).neg) (IntRatio.neg_neg (b.mul c))).trans
    (IntRatio.add_comm (a.mul d).neg (b.mul c))
  have expand := (IntRatio.mul_congr step (IntRatio.equivalent_refl c)).trans
    ((IntRatio.add_mul a (h.mul d) c).trans
      (IntRatio.add_congr (IntRatio.equivalent_refl (a.mul c))
        ((IntRatio.mul_assoc h d c).trans (IntRatio.mul_congr (IntRatio.equivalent_refl h) (IntRatio.mul_comm d c)))))
  have remaining := (IntRatio.sub_congr expand (IntRatio.mul_add a c h)).trans
    ((sub_common (IntRatio.finite_mul fa (IntRatio.finite_mul (x := IntRatio.two) True.intro hx))
        (h.mul (c.mul d)) (a.mul h)).trans
      ((IntRatio.sub_congr (IntRatio.equivalent_refl (h.mul (c.mul d))) (IntRatio.mul_comm a h)).trans
        ((IntRatio.mul_sub h (c.mul d) a).symm.trans
          (IntRatio.mul_congr (IntRatio.equivalent_refl h) (step_numerator x h hx)))))
  have linear := (kappa_jet x).right.left
  IntRatio.mul_cancel_left uDen
    ((IntRatio.mul_sub den ((b.inv.sub a.inv).mul h.inv) (kappaJetAt x).first).trans
      ((IntRatio.sub_congr scaledSlope
          ((IntRatio.mul_congr (IntRatio.equivalent_refl den) linear).trans scaledLinear)).trans
        (reorder.trans (remaining.trans (mul_div_cancel numerator uDen).symm))))

end Omega.Jet2
