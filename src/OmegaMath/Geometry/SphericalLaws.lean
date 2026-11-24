module
prelude
public import OmegaMath.Geometry.BargmannGram
import OmegaMath.Geometry.BargmannGram.Fractions
import OmegaMath.Geometry.BargmannGram.Polynomial

/-!
Omega original.

Rational spherical sine and Pythagorean laws for nonzero integer quaternion representatives.
-/

noncomputable section

@[expose] public section

namespace Omega.Geometry.SphericalLaws

open BargmannGram

def spread (a b : Quad4) : IntRatio := (IntRatio.ofInt Int.one).sub (kappa a b)

/-- The spread at vertex `a` between the sides toward `b` and `c`. -/
def vertexSpread (a b c : Quad4) : IntRatio :=
  (detGram3 a b c).mul ((spread a b).mul (spread c a)).inv

private def edgeDenominator (a b : Quad4) : Nat := a.normSq.mul b.normSq

private def spreadNumerator (a b : Quad4) : Int :=
  ((a.dot a).mul (b.dot b)).sub (Int.square (a.dot b))

private theorem spread_value (a b : Quad4) (hd : Not (Eq (edgeDenominator a b) Nat.zero)) :
    IntRatio.Equivalent (spread a b)
      (IntRatio.value (spreadNumerator a b) (edgeDenominator a b)) :=
  let d := edgeDenominator a b
  have cast : Eq (Int.ofNat d) ((a.dot a).mul (b.dot b)) :=
    Eq.map₂ Int.mul a.normSq_cast b.normSq_cast
  have one : IntRatio.Equivalent (IntRatio.ofInt Int.one) (IntRatio.value (Int.ofNat d) d) :=
    (IntRatio.value_self d hd).symm
  let p := Int.square (a.dot b)
  (IntRatio.sub_congr one (IntRatio.equivalent_refl (kappa a b))).trans
    ((value_sub_same (Int.ofNat d) p d).trans
      (Eq.subst (fun n : Int => IntRatio.Equivalent (IntRatio.value ((Int.ofNat d).sub p) d)
        (IntRatio.value (n.sub p) d)) cast (IntRatio.equivalent_refl _)))

private theorem spread_mul_value (a b c : Quad4)
    (hab : Not (Eq (edgeDenominator a b) Nat.zero))
    (hca : Not (Eq (edgeDenominator c a) Nat.zero)) :
    IntRatio.Equivalent ((spread a b).mul (spread c a))
      (IntRatio.value ((spreadNumerator a b).mul (spreadNumerator c a))
        ((edgeDenominator a b).mul (edgeDenominator c a))) :=
  (IntRatio.mul_congr (spread_value a b hab) (spread_value c a hca)).trans
    (Eq.subst (fun x => IntRatio.Equivalent _ x) (IntRatio.value_mul _ _ _ _)
      (IntRatio.equivalent_refl _))

private theorem spread_numerator_ne_zero (a b : Quad4)
    (hd : Not (Eq (edgeDenominator a b) Nat.zero))
    (hs : Not (IntRatio.Equivalent (spread a b) (IntRatio.ofInt Int.zero))) :
    Not (Eq (spreadNumerator a b) Int.zero) :=
  fun h => hs ((spread_value a b hd).trans
    (Eq.subst (fun n => IntRatio.Equivalent (IntRatio.value n (edgeDenominator a b))
      (IntRatio.ofInt Int.zero)) h.symm (IntRatio.value_zero _ hd)))

private theorem value_mul_inv_cancel {x : IntRatio} {n : Int} {d : Nat}
    (hx : IntRatio.Equivalent x (IntRatio.value n d))
    (hn : Not (Eq n Int.zero)) (hd : Not (Eq d Nat.zero)) :
    IntRatio.Equivalent (x.mul x.inv) (IntRatio.ofInt Int.one) :=
  (IntRatio.mul_congr hx (IntRatio.inv_congr hx)).trans
    ((Nat.rec (motive := fun d =>
        Not (Eq d Nat.zero) → IntRatio.Equivalent
          ((IntRatio.value n d).mul (IntRatio.value n d).inv) (IntRatio.ofInt Int.one))
      (fun h => False.elim (h Eq.refl))
      (fun k _ _ => IntRatio.mul_inv_cancel n k hn) d) hd)

private theorem spread_mul_unit (a b c : Quad4)
    (hab : Not (Eq (edgeDenominator a b) Nat.zero))
    (hca : Not (Eq (edgeDenominator c a) Nat.zero))
    (sab : Not (IntRatio.Equivalent (spread a b) (IntRatio.ofInt Int.zero)))
    (sca : Not (IntRatio.Equivalent (spread c a) (IntRatio.ofInt Int.zero))) :
    IntRatio.Equivalent (((spread a b).mul (spread c a)).mul
      ((spread a b).mul (spread c a)).inv) (IntRatio.ofInt Int.one) :=
  value_mul_inv_cancel (spread_mul_value a b c hab hca)
    (Int.mul_ne_zero (spread_numerator_ne_zero a b hab sab)
      (spread_numerator_ne_zero c a hca sca)) (nat_mul_ne_zero hab hca)

private theorem mul_cancel_pair (x d e : IntRatio)
    (h : IntRatio.Equivalent (d.mul e) (IntRatio.ofInt Int.one)) :
    IntRatio.Equivalent ((x.mul d).mul e) x :=
  (IntRatio.mul_assoc x d e).trans
    ((IntRatio.mul_congr (IntRatio.equivalent_refl x) h).trans (IntRatio.mul_one x))

private theorem quotient_eq_iff (x y d : IntRatio)
    (h : IntRatio.Equivalent (d.mul d.inv) (IntRatio.ofInt Int.one)) :
    Iff (IntRatio.Equivalent (x.mul d.inv) y) (IntRatio.Equivalent x (y.mul d)) :=
  Iff.intro
    (fun e => (mul_cancel_pair x d.inv d ((IntRatio.mul_comm d.inv d).trans h)).symm.trans
      (IntRatio.mul_congr e (IntRatio.equivalent_refl d)))
    (fun e => (IntRatio.mul_congr e (IntRatio.equivalent_refl d.inv)).trans
      (mul_cancel_pair y d d.inv h))

open Polynomial

private def gramExpr (A B C p q r : Expr) : Expr :=
  (((A.mul B).mul C).add ((Expr.const Int.two).mul ((p.mul q).mul r))).sub
    (((p.sq.mul C).add (q.sq.mul A)).add (r.sq.mul B))

private def bindGram (a b c : Quad4) : Nat → Int :=
  Expr.bind (a.dot a) (Expr.bind (b.dot b) (Expr.bind (c.dot c)
    (Expr.bind (a.dot b) (Expr.bind (b.dot c) (Expr.bind (c.dot a) (fun _ => Int.zero))))))

private theorem detGram3_cyclic (a b c : Quad4) (ha : Not (Eq a Quad4.zero))
    (hb : Not (Eq b Quad4.zero)) (hc : Not (Eq c Quad4.zero)) :
    IntRatio.Equivalent (detGram3 a b c) (detGram3 b c a) :=
  let A := Expr.var Nat.zero
  let B := Expr.var Nat.zero.succ
  let C := Expr.var Nat.zero.succ.succ
  let p := Expr.var Nat.zero.succ.succ.succ
  let q := Expr.var Nat.zero.succ.succ.succ.succ
  let r := Expr.var Nat.zero.succ.succ.succ.succ.succ
  have num : Eq (gramNumeratorOf a b c) (gramNumeratorOf b c a) :=
    Expr.certify (bindGram a b c) (gramExpr A B C p q r) (gramExpr B C A q r p) Eq.refl
  have den : Eq (gramDenominator a b c) (gramDenominator b c a) :=
    (Nat.mul_assoc a.normSq b.normSq c.normSq).trans (Nat.mul_comm _ _)
  (detGram3_value a b c ha hb hc).trans
    ((Eq.subst (fun x => IntRatio.Equivalent _ x) (Eq.map₂ IntRatio.value num den)
      (IntRatio.equivalent_refl _)).trans (detGram3_value b c a hb hc ha).symm)

private theorem sine_cyclic (a b c : Quad4)
    (ha : Not (Eq a Quad4.zero)) (hb : Not (Eq b Quad4.zero)) (hc : Not (Eq c Quad4.zero))
    (sab : Not (IntRatio.Equivalent (spread a b) (IntRatio.ofInt Int.zero)))
    (sbc : Not (IntRatio.Equivalent (spread b c) (IntRatio.ofInt Int.zero)))
    (sca : Not (IntRatio.Equivalent (spread c a) (IntRatio.ofInt Int.zero))) :
    IntRatio.Equivalent ((vertexSpread a b c).mul (spread b c).inv)
      ((vertexSpread b c a).mul (spread c a).inv) :=
  let x := spread a b
  let y := spread b c
  let z := spread c a
  let target := (vertexSpread b c a).mul z.inv
  have hab := nat_mul_ne_zero (a.normSq_ne_zero ha) (b.normSq_ne_zero hb)
  have hbc := nat_mul_ne_zero (b.normSq_ne_zero hb) (c.normSq_ne_zero hc)
  have hca := nat_mul_ne_zero (c.normSq_ne_zero hc) (a.normSq_ne_zero ha)
  have unitY := value_mul_inv_cancel (spread_value b c hbc) (spread_numerator_ne_zero b c hbc sbc) hbc
  have unitZ := value_mul_inv_cancel (spread_value c a hca) (spread_numerator_ne_zero c a hca sca) hca
  have unitXZ := spread_mul_unit a b c hab hca sab sca
  have unitYX := spread_mul_unit b c a hbc hab sbc sab
  have rotate : IntRatio.Equivalent (y.mul (x.mul z)) (z.mul (y.mul x)) :=
    (IntRatio.mul_assoc y x z).symm.trans (IntRatio.mul_comm (y.mul x) z)
  have reorder : IntRatio.Equivalent ((target.mul y).mul (x.mul z))
      ((target.mul z).mul (y.mul x)) :=
    (IntRatio.mul_assoc target y (x.mul z)).trans
      ((IntRatio.mul_congr (IntRatio.equivalent_refl target) rotate).trans
        (IntRatio.mul_assoc target z (y.mul x)).symm)
  have clearZ := mul_cancel_pair (vertexSpread b c a) z.inv z
    ((IntRatio.mul_comm z.inv z).trans unitZ)
  have clearYX := mul_cancel_pair (detGram3 b c a) (y.mul x).inv (y.mul x)
    ((IntRatio.mul_comm (y.mul x).inv (y.mul x)).trans unitYX)
  have clearRight := reorder.trans
    ((IntRatio.mul_congr clearZ (IntRatio.equivalent_refl (y.mul x))).trans clearYX)
  (quotient_eq_iff (vertexSpread a b c) target y unitY).mpr
    ((quotient_eq_iff (detGram3 a b c) (target.mul y) (x.mul z) unitXZ).mpr
      ((detGram3_cyclic a b c ha hb hc).trans clearRight.symm))

/-- The ratios of vertex spread to opposite side spread agree around the triangle. -/
theorem rational_spherical_sine_law (a b c : Quad4)
    (ha : Not (Eq a Quad4.zero)) (hb : Not (Eq b Quad4.zero)) (hc : Not (Eq c Quad4.zero))
    (sab : Not (IntRatio.Equivalent (spread a b) (IntRatio.ofInt Int.zero)))
    (sbc : Not (IntRatio.Equivalent (spread b c) (IntRatio.ofInt Int.zero)))
    (sca : Not (IntRatio.Equivalent (spread c a) (IntRatio.ofInt Int.zero))) :
    And (IntRatio.Equivalent ((vertexSpread a b c).mul (spread b c).inv)
          ((vertexSpread b c a).mul (spread c a).inv))
        (IntRatio.Equivalent ((vertexSpread b c a).mul (spread c a).inv)
          ((vertexSpread c a b).mul (spread a b).inv)) :=
  And.intro (sine_cyclic a b c ha hb hc sab sbc sca) (sine_cyclic b c a hb hc ha sbc sca sab)

private theorem vertex_denominator (a b c : Quad4) :
    Eq ((edgeDenominator a b).mul (edgeDenominator c a))
      ((gramDenominator a b c).mul a.normSq) :=
  (Nat.mul_assoc (edgeDenominator a b) c.normSq a.normSq).symm

/-- The squared cosine of the opposite side is the product for the two incident sides. -/
theorem rational_spherical_pythagorean (a b c : Quad4)
    (ha : Not (Eq a Quad4.zero)) (hb : Not (Eq b Quad4.zero)) (hc : Not (Eq c Quad4.zero))
    (right : Eq ((a.dot a).mul (b.dot c)) ((a.dot b).mul (a.dot c))) :
    IntRatio.Equivalent (kappa b c) ((kappa a b).mul (kappa c a)) :=
  let A := a.normSq
  let d := A.mul A
  let p := a.dot b
  let q := b.dot c
  let r := c.dot a
  let oppositeDen := edgeDenominator b c
  let incidentDen := (edgeDenominator a b).mul (edgeDenominator c a)
  let oppositeNum := Int.square q
  let incidentNum := (Int.square p).mul (Int.square r)
  have hA := a.normSq_ne_zero ha
  have hB := b.normSq_ne_zero hb
  have hC := c.normSq_ne_zero hc
  have den : Eq (oppositeDen.mul d) incidentDen :=
    (Nat.mul_assoc oppositeDen A A).symm.trans
      ((congrArg (fun n : Nat => n.mul A) ((Nat.mul_comm oppositeDen A).trans
        (Nat.mul_assoc A b.normSq c.normSq).symm)).trans (vertex_denominator a b c).symm)
  have dot : Eq (q.mul (Int.ofNat A)) (p.mul r) :=
    (Int.mul_comm q (Int.ofNat A)).trans
      ((congrArg (fun n : Int => n.mul q) a.normSq_cast).trans
        (right.trans (congrArg p.mul (a.dot_comm c))))
  have num : Eq (oppositeNum.mul (Int.ofNat d)) incidentNum :=
    (Int.square_mul q (Int.ofNat A)).symm.trans
      ((congrArg Int.square dot).trans (Int.square_mul p r))
  have cross : Eq (oppositeNum.mul (Int.ofNat incidentDen))
      (incidentNum.mul (Int.ofNat oppositeDen)) :=
    (congrArg oppositeNum.mul (congrArg Int.ofNat den.symm)).trans
      ((Int.mul_assoc oppositeNum (Int.ofNat oppositeDen) (Int.ofNat d)).symm.trans
        ((Int.mul_right_comm oppositeNum (Int.ofNat oppositeDen) (Int.ofNat d)).trans
          (congrArg (fun n : Int => n.mul (Int.ofNat oppositeDen)) num)))
  have comparison := (IntRatio.value_cross_iff oppositeNum incidentNum oppositeDen incidentDen
    (nat_mul_ne_zero hB hC) (nat_mul_ne_zero (nat_mul_ne_zero hA hB) (nat_mul_ne_zero hC hA))).mpr cross
  have product := IntRatio.value_mul (Int.square p) (Int.square r)
    (edgeDenominator a b) (edgeDenominator c a)
  Eq.subst (fun x => IntRatio.Equivalent (kappa b c) x) product.symm comparison

/-- The Schur complement at `a` expresses the Gram deficit as an integer square. -/
private theorem gram_deficit (a b c : Quad4) :
    Eq (((spreadNumerator a b).mul (spreadNumerator c a)).sub
      ((gramNumeratorOf a b c).mul (a.dot a)))
      (Int.square (((a.dot a).mul (b.dot c)).sub ((a.dot b).mul (c.dot a)))) :=
  let A := Expr.var Nat.zero
  let B := Expr.var Nat.zero.succ
  let C := Expr.var Nat.zero.succ.succ
  let p := Expr.var Nat.zero.succ.succ.succ
  let q := Expr.var Nat.zero.succ.succ.succ.succ
  let r := Expr.var Nat.zero.succ.succ.succ.succ.succ
  Expr.certify (bindGram a b c)
    ((((A.mul B).sub p.sq).mul ((C.mul A).sub r.sq)).sub ((gramExpr A B C p q r).mul A))
    (((A.mul q).sub (p.mul r)).sq) Eq.refl

private theorem value_eq_iff {n m : Int} {d : Nat} (hd : Not (Eq d Nat.zero)) :
    Iff (IntRatio.Equivalent (IntRatio.value n d) (IntRatio.value m d)) (Eq n m) :=
  Iff.intro
    (fun h => Int.eq_of_mul_eq_mul_right (fun h => hd (Int.ofNat_inj.mp h))
      ((IntRatio.value_cross_iff n m d d hd hd).mp h))
    (fun h => Eq.subst (fun t => IntRatio.Equivalent (IntRatio.value n d) (IntRatio.value t d))
      h (IntRatio.equivalent_refl _))

/-- A right vertex has spread one, and spread one forces the right-angle dot identity.
The two incident sides must have nonzero spread. -/
theorem right_iff_vertexSpread_one (a b c : Quad4)
    (ha : Not (Eq a Quad4.zero)) (hb : Not (Eq b Quad4.zero)) (hc : Not (Eq c Quad4.zero))
    (sab : Not (IntRatio.Equivalent (spread a b) (IntRatio.ofInt Int.zero)))
    (sca : Not (IntRatio.Equivalent (spread c a) (IntRatio.ofInt Int.zero))) :
    Iff (Eq ((a.dot a).mul (b.dot c)) ((a.dot b).mul (a.dot c)))
      (IntRatio.Equivalent (vertexSpread a b c) (IntRatio.ofInt Int.one)) :=
  let g := detGram3 a b c
  let s := (spread a b).mul (spread c a)
  let d := (edgeDenominator a b).mul (edgeDenominator c a)
  let n := (gramNumeratorOf a b c).mul (a.dot a)
  let m := (spreadNumerator a b).mul (spreadNumerator c a)
  have hA := a.normSq_ne_zero ha
  have hab := nat_mul_ne_zero hA (b.normSq_ne_zero hb)
  have hca := nat_mul_ne_zero (c.normSq_ne_zero hc) hA
  have unitS := spread_mul_unit a b c hab hca sab sca
  have quotient := quotient_eq_iff g (IntRatio.ofInt Int.one) s unitS
  have oneMul := (IntRatio.mul_comm (IntRatio.ofInt Int.one) s).trans (IntRatio.mul_one s)
  have scale := (IntRatio.value_scale_of_ne_zero (gramNumeratorOf a b c)
    (gramDenominator a b c) a.normSq hA).symm
  have change : Eq (IntRatio.value ((gramNumeratorOf a b c).mul (Int.ofNat a.normSq))
      ((gramDenominator a b c).mul a.normSq)) (IntRatio.value n d) :=
    Eq.map₂ IntRatio.value (congrArg (gramNumeratorOf a b c).mul a.normSq_cast)
      (vertex_denominator a b c).symm
  have gramValue := (detGram3_value a b c ha hb hc).trans
    (scale.trans (Eq.subst (fun t => IntRatio.Equivalent _ t) change (IntRatio.equivalent_refl _)))
  have spreadValue := spread_mul_value a b c hab hca
  have sameDen := value_eq_iff (n := n) (m := m) (nat_mul_ne_zero hab hca)
  have flip := congrArg (a.dot b).mul (a.dot_comm c)
  Iff.intro
    (fun right =>
      have residual := Int.sub_eq_zero.mpr (right.trans flip)
      have equal := (Int.sub_eq_zero.mp ((gram_deficit a b c).trans
        (congrArg Int.square residual))).symm
      quotient.mpr (gramValue.trans ((sameDen.mpr equal).trans
        (spreadValue.symm.trans oneMul.symm))))
    (fun unit =>
      have equal := sameDen.mp (gramValue.symm.trans
        ((quotient.mp unit).trans (oneMul.trans spreadValue)))
      have square := (gram_deficit a b c).symm.trans (Int.sub_eq_zero.mpr equal.symm)
      have residual := (Int.mul_eq_zero.mp square).elim (fun h => h) (fun h => h)
      (Int.sub_eq_zero.mp residual).trans flip.symm)

end Omega.Geometry.SphericalLaws
