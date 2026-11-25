/- GID: D5/S3/Calculus/MidpointDrift
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Quaternion norm drift for rational steps at arbitrary sampling weights. -/

/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Data.Int.Basic
import all OmegaInit.Prelude
import D5.S3.Geometry.BargmannGram.Fractions
public import D5.S3.Geometry.Ternion.Heap.Fidelity
public import D5.S3.Calculus.Jet2.Scalar

/-!
Omega original.

Rational quaternion steps with a pure generator, the exact norm drift at
arbitrary sampling weight, and the norm and projective fidelity at the midpoint.
-/

noncomputable section

@[expose] public section

namespace Omega.Calculus.MidpointDrift

open Quaternion

/-- A rational quaternion with a common positive denominator `denPred.succ`. -/
structure RationalQuaternion where
  num : Quaternion
  denPred : Nat

namespace RationalQuaternion

def den (x : RationalQuaternion) : Nat := x.denPred.succ

def Equivalent (x y : RationalQuaternion) : Prop :=
  Eq (scale (Int.ofNat y.den) x.num) (scale (Int.ofNat x.den) y.num)

def sub (x y : RationalQuaternion) : RationalQuaternion :=
  ⟨(scale (Int.ofNat y.den) x.num).sub (scale (Int.ofNat x.den) y.num),
    IntRatio.mulDenPred x.denPred y.denPred⟩

def normSq (x : RationalQuaternion) : IntRatio :=
  IntRatio.value (Int.ofNat x.num.normSq) (x.den.mul x.den)

def IsUnit (x : RationalQuaternion) : Prop := IntRatio.Equivalent x.normSq IntRatio.one

theorem nonzero_of_isUnit {x : RationalQuaternion} (h : x.IsUnit) : x.num.Nonzero :=
  have denNe := Ternion.nat_mul_ne_zero (Nat.succ_ne_zero x.denPred) (Nat.succ_ne_zero x.denPred)
  have cross := (IntRatio.value_cross_iff (Int.ofNat x.num.normSq) Int.one (x.den.mul x.den)
    Nat.zero.succ denNe (Nat.succ_ne_zero Nat.zero)).mp h
  nonzero_of_normSq_ne_zero (fun hn => denNe (Int.ofNat_inj.mp
    (((Int.one_mul (Int.ofNat (x.den.mul x.den))).symm.trans cross.symm).trans
      ((Int.mul_one (Int.ofNat x.num.normSq)).trans (congrArg Int.ofNat hn)))))

end RationalQuaternion

/-- The numerator of `1 + α A`, where `α = p / qPred.succ`. -/
def alphaStepLeft (p : Int) (qPred : Nat) (a : RationalQuaternion) : Quaternion :=
  (scalar ((Int.ofNat qPred.succ).mul (Int.ofNat a.den))).add (scale p a.num)

/-- The numerator of `1 - (1 - α) A` with the same denominator as `1 + α A`. -/
def alphaStepRight (p : Int) (qPred : Nat) (a : RationalQuaternion) : Quaternion :=
  (scalar ((Int.ofNat qPred.succ).mul (Int.ofNat a.den))).add
    (scale (p.sub (Int.ofNat qPred.succ)) a.num)

/-- The equation `(1 + α A) x = (1 - (1 - α) A) x₀` after clearing denominators. -/
def AlphaStepEquation (p : Int) (qPred : Nat) (a x₀ x : RationalQuaternion) : Prop :=
  Eq ((alphaStepLeft p qPred a).mul (scale (Int.ofNat x₀.den) x.num))
     ((alphaStepRight p qPred a).mul (scale (Int.ofNat x.den) x₀.num))

/-- The conjugate inverts the cleared left factor after division by its nonzero squared norm. -/
theorem alpha_step_denominator_invertible (p : Int) (qPred : Nat)
    (a : RationalQuaternion) (pure : Eq a.num.w Int.zero) :
    let l := alphaStepLeft p qPred a
    And (Not (Eq l.normSq Nat.zero))
      (And (Eq (l.mul l.conj) (scalar (Int.ofNat l.normSq)))
           (Eq (l.conj.mul l) (scalar (Int.ofNat l.normSq)))) :=
  let t := (Int.ofNat qPred.succ).mul (Int.ofNat a.den)
  let l := alphaStepLeft p qPred a
  have realPart : Eq l.w t :=
    (congrArg (fun w : Int => t.add (p.mul w)) pure).trans
      ((congrArg t.add (Int.mul_zero p)).trans (Int.add_zero t))
  have nonzero : l.Nonzero := fun h =>
    Int.mul_ne_zero (Int.ofNat_succ_ne_zero qPred) (Int.ofNat_succ_ne_zero a.denPred)
      (realPart.symm.trans h.left)
  And.intro (normSq_ne_zero nonzero) (And.intro (mul_conj_eq_normSq l) (conj_mul_eq_normSq l))

private theorem succ_pred_of_ne_zero (n : Nat) (h : Not (Eq n Nat.zero)) :
    Eq n.pred.succ n :=
  (Nat.rec (motive := fun n => Not (Eq n Nat.zero) → Eq n.pred.succ n)
    (fun h => False.elim (h rfl)) (fun k _ _ => congrArg Nat.succ (Nat.pred_succ k)) n) h

/-- Apply the inverse explicitly using the squared norm of the cleared left factor. -/
def alphaStep (p : Int) (qPred : Nat) (a x₀ : RationalQuaternion) : RationalQuaternion :=
  let l := alphaStepLeft p qPred a
  let r := alphaStepRight p qPred a
  ⟨l.conj.mul (r.mul x₀.num), IntRatio.mulDenPred l.normSq.pred x₀.denPred⟩

private theorem alpha_step_den (p : Int) (qPred : Nat) (a x₀ : RationalQuaternion)
    (nonzero : Not (Eq (alphaStepLeft p qPred a).normSq Nat.zero)) :
    Eq (Int.ofNat (alphaStep p qPred a x₀).den)
      ((Int.ofNat x₀.den).mul (Int.ofNat (alphaStepLeft p qPred a).normSq)) :=
  let n := (alphaStepLeft p qPred a).normSq
  (IntRatio.denominator_mul n.pred x₀.denPred).trans
    ((congrArg (fun v : Nat => (Int.ofNat v).mul (Int.ofNat x₀.den))
      (succ_pred_of_ne_zero n nonzero)).trans (Int.mul_comm _ _))

/-- The explicit step solves the implicit rational quaternion equation. -/
theorem alpha_step_equation (p : Int) (qPred : Nat) (a x₀ : RationalQuaternion)
    (pure : Eq a.num.w Int.zero) :
    AlphaStepEquation p qPred a x₀ (alphaStep p qPred a x₀) :=
  let l := alphaStepLeft p qPred a
  let r := alphaStepRight p qPred a
  let x := alphaStep p qPred a x₀
  have hl := alpha_step_denominator_invertible p qPred a pure
  have den := alpha_step_den p qPred a x₀ hl.left
  have product : Eq (l.mul x.num) (scale (Int.ofNat l.normSq) (r.mul x₀.num)) :=
    (mul_assoc l l.conj (r.mul x₀.num)).symm.trans
      ((congrArg (fun v : Quaternion => v.mul (r.mul x₀.num)) hl.right.left).trans
        (scalar_mul _ _))
  (scale_mul_right _ l x.num).trans
    ((congrArg (scale (Int.ofNat x₀.den)) product).trans
      ((scale_mul _ _ _).trans
        ((congrArg (fun k : Int => scale k (r.mul x₀.num)) den.symm).trans
          (scale_mul_right _ r x₀.num).symm)))

/-- Any solution represents the same rational quaternion as the explicit step. -/
theorem alpha_step_unique (p : Int) (qPred : Nat) (a x₀ x : RationalQuaternion)
    (pure : Eq a.num.w Int.zero) (hx : AlphaStepEquation p qPred a x₀ x) :
    x.Equivalent (alphaStep p qPred a x₀) :=
  let l := alphaStepLeft p qPred a
  let r := alphaStepRight p qPred a
  let dx := Int.ofNat x.den
  let d₀ := Int.ofNat x₀.den
  let n := Int.ofNat l.normSq
  have hl := alpha_step_denominator_invertible p qPred a pure
  have cancel : Eq (l.conj.mul (l.mul x.num)) (scale n x.num) :=
    (mul_assoc l.conj l x.num).symm.trans
      ((congrArg (fun t : Quaternion => t.mul x.num) hl.right.right).trans (scalar_mul _ _))
  (congrArg (fun k : Int => scale k x.num) (alpha_step_den p qPred a x₀ hl.left)).trans
    ((scale_mul x.num d₀ n).symm.trans
      ((congrArg (scale d₀) cancel.symm).trans
        ((scale_mul_right d₀ l.conj (l.mul x.num)).symm.trans
          ((congrArg l.conj.mul (scale_mul_right d₀ l x.num).symm).trans
            ((congrArg l.conj.mul hx).trans
              ((congrArg l.conj.mul (scale_mul_right dx r x₀.num)).trans
                (scale_mul_right dx l.conj (r.mul x₀.num))))))))

open Quaternion.Polynomial

private def inputs (a : Quaternion) (rest : Values) : Values :=
  .cons a.w (.cons a.x (.cons a.y (.cons a.z rest)))

private def polynomialAdd (a b : Coordinates) : Coordinates :=
  ⟨a.w.add b.w, a.x.add b.x, a.y.add b.y, a.z.add b.z⟩

private def polynomialSub (a b : Coordinates) : Coordinates :=
  ⟨a.w.sub b.w, a.x.sub b.x, a.y.sub b.y, a.z.sub b.z⟩

private def four : Nat := Nat.zero.succ.succ.succ.succ

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem cleared_difference (t p q : Int) (a b c : Quaternion) :
    Eq (((scalar t).add (scale p a)).mul b |>.sub
          (((scalar t).add (scale (p.sub q) a)).mul c))
      ((scale t (b.sub c)).add (a.mul ((scale p b).add (scale (q.sub p) c)))) :=
  let values := Values.cons t (.cons p (.cons q (inputs a (inputs b (inputs c .nil)))))
  let T := Expr.var Nat.zero
  let P := Expr.var Nat.zero.succ
  let Q := Expr.var Nat.zero.succ.succ
  let offset := Nat.zero.succ.succ.succ
  let A := Coordinates.variables offset
  let B := Coordinates.variables (offset.add four)
  let C := Coordinates.variables ((offset.add four).add four)
  let L := polynomialAdd (Coordinates.scalar T) (A.scale P)
  let R := polynomialAdd (Coordinates.scalar T) (A.scale (P.sub Q))
  let lhs := polynomialSub (L.mul B) (R.mul C)
  let rhs := polynomialAdd ((polynomialSub B C).scale T)
    (A.mul (polynomialAdd (B.scale P) (C.scale (Q.sub P))))
  Quaternion.ext (lhs.w.sound rhs.w values rfl) (lhs.x.sound rhs.x values rfl)
    (lhs.y.sound rhs.y values rfl) (lhs.z.sound rhs.z values rfl)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem dot_add_left (a b c : Quaternion) :
    Eq ((a.add b).dot c) ((a.dot c).add (b.dot c)) :=
  let values := inputs a (inputs b (inputs c .nil))
  let A := Coordinates.variables Nat.zero
  let B := Coordinates.variables four
  let C := Coordinates.variables (four.add four)
  ((polynomialAdd A B).dot C).sound ((A.dot C).add (B.dot C)) values rfl

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem dot_mul_self_of_pure (a v : Quaternion) (pure : Eq a.w Int.zero) :
    Eq ((a.mul v).dot v) Int.zero :=
  let values := inputs a (inputs v .nil)
  let A := Coordinates.variables Nat.zero
  let V := Coordinates.variables four
  (((A.mul V).dot V).sound (A.w.mul (V.dot V)) values rfl).trans
    ((congrArg (fun k : Int => k.mul (v.dot v)) pure).trans (Int.zero_mul _))

private theorem zero_of_sub_eq {a b : Quaternion} (h : Eq a b) :
    Eq (a.sub b) zero :=
  Quaternion.ext (Int.sub_eq_zero.mpr (congrArg Quaternion.w h))
    (Int.sub_eq_zero.mpr (congrArg Quaternion.x h))
    (Int.sub_eq_zero.mpr (congrArg Quaternion.y h))
    (Int.sub_eq_zero.mpr (congrArg Quaternion.z h))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem zero_dot (v : Quaternion) : Eq (zero.dot v) Int.zero :=
  Eq.map₂ Int.add (Eq.map₂ Int.add (Int.zero_mul v.w) (Int.zero_mul v.x))
    (Eq.map₂ Int.add (Int.zero_mul v.y) (Int.zero_mul v.z))

private theorem dot_difference (t p q : Int) (a b c : Quaternion)
    (ht : Not (Eq t Int.zero)) (pure : Eq a.w Int.zero)
    (h : Eq (((scalar t).add (scale p a)).mul b)
      (((scalar t).add (scale (p.sub q) a)).mul c)) :
    Eq ((b.sub c).dot ((scale p b).add (scale (q.sub p) c))) Int.zero :=
  let u := b.sub c
  let v := (scale p b).add (scale (q.sub p) c)
  have fromEquation : Eq (((scale t u).add (a.mul v)).dot v) Int.zero :=
    (congrArg (fun z : Quaternion => z.dot v)
      ((cleared_difference t p q a b c).symm.trans (zero_of_sub_eq h))).trans (zero_dot v)
  have expansion : Eq (((scale t u).add (a.mul v)).dot v) (t.mul (u.dot v)) :=
    (dot_add_left (scale t u) (a.mul v) v).trans
      ((Eq.map₂ Int.add (dot_scale t u v) (dot_mul_self_of_pure a v pure)).trans (Int.add_zero _))
  Int.eq_of_mul_eq_mul_left ht
    (expansion.symm.trans (fromEquation.trans (Int.mul_zero t).symm))

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
/-- Polarization isolates the term that vanishes by the step equation. -/
private theorem norm_difference_identity (p q : Int) (b c : Quaternion) :
    Eq (q.mul ((b.dot b).sub (c.dot c)))
      (((q.sub (Int.two.mul p)).mul ((b.sub c).dot (b.sub c))).add
        (Int.two.mul ((b.sub c).dot ((scale p b).add (scale (q.sub p) c))))) :=
  let values := Values.cons p (.cons q (inputs b (inputs c .nil)))
  let P := Expr.var Nat.zero
  let Q := Expr.var Nat.zero.succ
  let two := Expr.one.double
  let offset := Nat.zero.succ.succ
  let B := Coordinates.variables offset
  let C := Coordinates.variables (offset.add four)
  let U := polynomialSub B C
  let V := polynomialAdd (B.scale P) (C.scale (Q.sub P))
  let lhs := Q.mul ((B.dot B).sub (C.dot C))
  let rhs := (((Q.sub (two.mul P)).mul (U.dot U)).add (two.mul (U.dot V)))
  lhs.sound rhs values rfl

private theorem cleared_norm_drift (p : Int) (qPred : Nat) (a x₀ x : RationalQuaternion)
    (pure : Eq a.num.w Int.zero) (h : AlphaStepEquation p qPred a x₀ x) :
    let q := Int.ofNat qPred.succ
    let b := scale (Int.ofNat x₀.den) x.num
    let c := scale (Int.ofNat x.den) x₀.num
    Eq (q.mul ((Int.ofNat b.normSq).sub (Int.ofNat c.normSq)))
      ((q.sub (Int.two.mul p)).mul (Int.ofNat (b.sub c).normSq)) :=
  let q := Int.ofNat qPred.succ
  let t := q.mul (Int.ofNat a.den)
  let b := scale (Int.ofNat x₀.den) x.num
  let c := scale (Int.ofNat x.den) x₀.num
  let u := b.sub c
  let drift := (q.sub (Int.two.mul p)).mul
  have ht := Int.mul_ne_zero (Int.ofNat_succ_ne_zero qPred) (Int.ofNat_succ_ne_zero a.denPred)
  have orthogonal := dot_difference t p q a.num b c ht pure h
  (congrArg q.mul (Eq.map₂ Int.sub b.normSq_cast c.normSq_cast)).trans
    ((norm_difference_identity p q b c).trans
      ((congrArg (drift (u.dot u)).add
        ((congrArg Int.two.mul orthogonal).trans (Int.mul_zero Int.two))).trans
        ((Int.add_zero _).trans (congrArg drift u.normSq_cast.symm))))

private theorem square_product (a b : Nat) :
    Eq ((a.mul b).mul (a.mul b)) ((a.mul a).mul (b.mul b)) :=
  (Nat.mul_assoc a b (a.mul b)).trans
    ((congrArg a.mul ((Nat.mul_assoc b a b).symm.trans
      ((congrArg (fun n : Nat => n.mul b) (Nat.mul_comm b a)).trans (Nat.mul_assoc a b b)))).trans
      (Nat.mul_assoc a a (b.mul b)).symm)

private theorem normSq_common (x : RationalQuaternion) (extraPred : Nat) :
    let extra := extraPred.succ
    let d := x.den.mul extra
    let n := (scale (Int.ofNat extra) x.num).normSq
    IntRatio.Equivalent (IntRatio.value (Int.ofNat n) (d.mul d)) x.normSq :=
  let extra := extraPred.succ
  let d := x.den.mul extra
  let n := (scale (Int.ofNat extra) x.num).normSq
  have align : Eq (IntRatio.value (Int.ofNat n) (d.mul d))
      (IntRatio.value ((Int.ofNat x.num.normSq).mul (Int.ofNat (extra.mul extra)))
        ((x.den.mul x.den).mul (extra.mul extra))) :=
    Eq.map₂ IntRatio.value (congrArg Int.ofNat (normSq_scale (Int.ofNat extra) x.num))
      (square_product x.den extra)
  Eq.subst (motive := fun z => IntRatio.Equivalent z x.normSq) align.symm
    (IntRatio.value_scale_of_ne_zero _ _ _
      (Ternion.nat_mul_ne_zero (Nat.succ_ne_zero extraPred) (Nat.succ_ne_zero extraPred)))

private theorem weight_factor (p : Int) (qPred : Nat) :
    Eq (IntRatio.one.sub (IntRatio.two.mul (IntRatio.fraction p qPred)))
      (IntRatio.fraction ((Int.ofNat qPred.succ).sub (Int.two.mul p)) qPred) :=
  let q := Int.ofNat qPred.succ
  let twice := Int.two.mul p
  (congrArg IntRatio.one.sub (congrArg (IntRatio.fraction twice) ((Nat.add_zero _).trans (Nat.one_mul qPred)))).trans
    (Eq.map₂ IntRatio.fraction
      (Eq.map₂ Int.add (Int.one_mul q) (Int.mul_one twice.neg)) ((Nat.add_zero _).trans (Nat.one_mul qPred)))

/-- Every solution satisfies the norm-drift identity, even for a nonunit initial value. -/
theorem alpha_sampling_norm_drift_of_equation (p : Int) (qPred : Nat)
    (a x₀ x : RationalQuaternion) (pure : Eq a.num.w Int.zero)
    (equation : AlphaStepEquation p qPred a x₀ x) :
    IntRatio.Equivalent (x.normSq.sub x₀.normSq)
      ((IntRatio.one.sub (IntRatio.two.mul (IntRatio.fraction p qPred))).mul
        (x.sub x₀).normSq) :=
  let q := qPred.succ
  let b := scale (Int.ofNat x₀.den) x.num
  let c := scale (Int.ofNat x.den) x₀.num
  let d := (x.sub x₀).den
  let e := d.mul d
  let leftNum := (Int.ofNat b.normSq).sub (Int.ofNat c.normSq)
  let delta := Int.ofNat (b.sub c).normSq
  let factor := (Int.ofNat q).sub (Int.two.mul p)
  have hd : Eq (x.den.mul x₀.den) d := IntRatio.nat_denominator_mul x.denPred x₀.denPred
  have bNorm := Eq.subst (motive := fun k : Nat =>
      IntRatio.Equivalent (IntRatio.value (Int.ofNat b.normSq) (k.mul k)) x.normSq)
    hd (normSq_common x x₀.denPred)
  have cNorm : IntRatio.Equivalent (IntRatio.value (Int.ofNat c.normSq) e) x₀.normSq :=
    Eq.subst (motive := fun k : Nat =>
      IntRatio.Equivalent (IntRatio.value (Int.ofNat c.normSq) (k.mul k)) x₀.normSq)
      ((Nat.mul_comm x₀.den x.den).trans hd) (normSq_common x₀ x.denPred)
  have difference : IntRatio.Equivalent (x.normSq.sub x₀.normSq) (IntRatio.value leftNum e) :=
    (IntRatio.sub_congr bNorm.symm cNorm.symm).trans
      (Geometry.BargmannGram.value_sub_same (Int.ofNat b.normSq) (Int.ofNat c.normSq) e)
  have eNe := Ternion.nat_mul_ne_zero (Nat.succ_ne_zero (x.sub x₀).denPred)
    (Nat.succ_ne_zero (x.sub x₀).denPred)
  have cross : Eq (leftNum.mul (Int.ofNat (q.mul e))) ((factor.mul delta).mul (Int.ofNat e)) :=
    (Int.mul_assoc leftNum (Int.ofNat q) (Int.ofNat e)).symm.trans
      ((congrArg (fun v : Int => v.mul (Int.ofNat e)) (Int.mul_comm leftNum (Int.ofNat q))).trans
        (congrArg (fun v : Int => v.mul (Int.ofNat e))
          (cleared_norm_drift p qPred a x₀ x pure equation)))
  have drift := (IntRatio.value_cross_iff leftNum (factor.mul delta) e (q.mul e) eNe
    (Ternion.nat_mul_ne_zero (Nat.succ_ne_zero qPred) eNe)).mpr cross
  have rightForm : Eq
      ((IntRatio.one.sub (IntRatio.two.mul (IntRatio.fraction p qPred))).mul (x.sub x₀).normSq)
      (IntRatio.value (factor.mul delta) (q.mul e)) :=
    (congrArg (fun v : IntRatio => v.mul (x.sub x₀).normSq) (weight_factor p qPred)).trans
      (IntRatio.value_mul factor delta q e)
  difference.trans (Eq.subst (motive := IntRatio.Equivalent (IntRatio.value leftNum e)) rightForm.symm drift)

/-- The drift of a step from a unit quaternion is `(1 − 2α) ‖x − x₀‖²`. -/
private theorem alpha_sampling_norm_drift_fraction (p : Int) (qPred : Nat) (a x₀ : RationalQuaternion)
    (pure : Eq a.num.w Int.zero) (unit : x₀.IsUnit) :
    let x := alphaStep p qPred a x₀
    IntRatio.Equivalent (x.normSq.sub IntRatio.one)
      ((IntRatio.one.sub (IntRatio.two.mul (IntRatio.fraction p qPred))).mul
        (x.sub x₀).normSq) :=
  let x := alphaStep p qPred a x₀
  (IntRatio.sub_congr (IntRatio.equivalent_refl x.normSq) unit.symm).trans
    (alpha_sampling_norm_drift_of_equation p qPred a x₀ x pure
      (alpha_step_equation p qPred a x₀ pure))

/-- Sample the implicit step at any finite rational weight. -/
def alphaSample (weight : IntRatio) (a x₀ : RationalQuaternion)
    (finite : weight.Finite) : RationalQuaternion :=
  (IntRatio.rec (motive := fun weight => weight.Finite → RationalQuaternion)
    (fun h => False.elim h) (fun p d _ => alphaStep p d a x₀) weight) finite

/-- The squared-norm drift is the squared displacement times `1 - 2α`. -/
theorem alpha_sampling_norm_drift (weight : IntRatio) (a x₀ : RationalQuaternion)
    (finite : weight.Finite) (pure : Eq a.num.w Int.zero) (unit : x₀.IsUnit) :
    let x := alphaSample weight a x₀ finite
    IntRatio.Equivalent (x.normSq.sub IntRatio.one)
      ((IntRatio.one.sub (IntRatio.two.mul weight)).mul (x.sub x₀).normSq) :=
  (IntRatio.rec (motive := fun weight => ∀ finite : weight.Finite,
    let x := alphaSample weight a x₀ finite
    IntRatio.Equivalent (x.normSq.sub IntRatio.one)
      ((IntRatio.one.sub (IntRatio.two.mul weight)).mul (x.sub x₀).normSq))
    (fun h => False.elim h)
    (fun p d _ => alpha_sampling_norm_drift_fraction p d a x₀ pure unit) weight) finite

/-- The step at sampling weight `1 / 2`. -/
def midpointStep (a x₀ : RationalQuaternion) : RationalQuaternion :=
  alphaStep Int.one Nat.zero.succ a x₀

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add Omega.Nat.mul Omega.Int.subNatNat in
private theorem midpointFactor : IntRatio.Equivalent
      (IntRatio.one.sub (IntRatio.two.mul (IntRatio.fraction Int.one Nat.zero.succ)))
      IntRatio.zero :=
  IntRatio.value_zero Nat.zero.succ.succ (Nat.succ_ne_zero Nat.zero.succ)

theorem midpoint_unit_norm (a x₀ : RationalQuaternion)
    (pure : Eq a.num.w Int.zero) (unit : x₀.IsUnit) : (midpointStep a x₀).IsUnit :=
  let x := midpointStep a x₀
  let y := (x.sub x₀).normSq
  have finite (z : RationalQuaternion) : z.normSq.Finite :=
    Eq.subst (motive := fun d => (IntRatio.value (Int.ofNat z.num.normSq) d).Finite)
      (IntRatio.nat_denominator_mul z.denPred z.denPred).symm True.intro
  have vanish := (alpha_sampling_norm_drift (IntRatio.fraction Int.one Nat.one) a x₀ True.intro pure unit).trans
    ((IntRatio.mul_congr_left midpointFactor y).trans (IntRatio.zero_mul (finite (x.sub x₀))))
  have recover : IntRatio.Equivalent ((x.normSq.sub IntRatio.one).add IntRatio.one) x.normSq :=
    (IntRatio.add_assoc x.normSq IntRatio.one.neg IntRatio.one).trans
      ((IntRatio.add_congr (IntRatio.equivalent_refl x.normSq)
        (IntRatio.add_left_neg (x := IntRatio.one) True.intro)).trans
        (IntRatio.add_zero x.normSq))
  recover.symm.trans ((IntRatio.add_congr_left vanish IntRatio.one).trans
    (IntRatio.zero_add IntRatio.one))

/-- Consecutive points in the ternion heap recurrence have the same projective fidelity. -/
theorem kappa_triad_succ (a b : Quaternion) (ha : a.Nonzero) (hb : b.Nonzero) :
    IntRatio.Equivalent (Ternion.kappa a b) (Ternion.kappa b (Ternion.triad b a b)) :=
  let p := a.conj.mul b
  let n := Int.ofNat a.normSq
  have conjNonzero : a.conj.Nonzero := nonzero_of_normSq_ne_zero
    (fun h => normSq_ne_zero ha ((normSq_conj a).symm.trans h))
  have hp : p.Nonzero := nonzero_mul conjNonzero hb
  have hn : Not (Eq n Int.zero) := fun h => normSq_ne_zero ha (Int.ofNat_inj.mp h)
  have first : Eq (a.mul p) (scale n b) :=
    (mul_assoc a a.conj b).symm.trans
      ((congrArg (fun q : Quaternion => q.mul b) (mul_conj_eq_normSq a)).trans (scalar_mul n b))
  have second : Eq (b.mul p) (Ternion.triad b a b) := (mul_assoc b a.conj b).symm
  (Ternion.kappa_mul_right p a b hp).symm.trans
    (Eq.subst (motive := fun v => IntRatio.Equivalent v (Ternion.kappa b (Ternion.triad b a b)))
      (Eq.map₂ Ternion.kappa first second).symm
      (Ternion.kappa_scale_left n b (Ternion.triad b a b) hn))

/-- The initial-to-midpoint and midpoint-to-ternary-extrapolation fidelities agree. -/
theorem midpoint_half_step_fidelity (a x₀ : RationalQuaternion)
    (pure : Eq a.num.w Int.zero) (unit : x₀.IsUnit) :
    let h := (midpointStep a x₀).num
    IntRatio.Equivalent (Ternion.kappa x₀.num h) (Ternion.kappa h (Ternion.triad h x₀.num h)) :=
  kappa_triad_succ x₀.num (midpointStep a x₀).num
    (RationalQuaternion.nonzero_of_isUnit unit)
    (RationalQuaternion.nonzero_of_isUnit (midpoint_unit_norm a x₀ pure unit))

end Omega.Calculus.MidpointDrift
