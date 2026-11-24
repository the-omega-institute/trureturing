/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Projective.Circle

/-!
Omega original.

Exact rational tangent arithmetic in the finite chart of the projective Cayley
circle. Undefined inputs and zero chart denominators give undefined ratios.
-/

noncomputable section

@[expose] public section

namespace Omega.Arithmetic

open Projective.Circle

/-- Read a homogeneous pair as a signed fraction with positive denominator. -/
def tangentChart (a : Coordinates) : IntRatio :=
  Int.rec (IntRatio.value a.p) (fun n => IntRatio.fraction a.p.neg n) a.q

/-- Tangent addition on finite ratios, with the pole represented by undefined. -/
def tangentAdd (x y : IntRatio) : IntRatio :=
  IntRatio.map₂ (fun p d r e =>
    tangentChart (projectiveMul p (IntRatio.denominator d) r (IntRatio.denominator e))) x y

/-- Tangent subtraction uses the negated second angle coordinate. -/
def tangentSub (x y : IntRatio) : IntRatio := tangentAdd x y.neg

theorem tangentChart_undefined_iff (a : Coordinates) :
    Iff (Eq (tangentChart a) IntRatio.undefined) (Eq a.q Int.zero) :=
  Int.rec (motive := fun q =>
    Iff (Eq (tangentChart ⟨a.p, q⟩) IntRatio.undefined) (Eq q Int.zero))
    (fun n =>
      let zero := IntRatio.value_undefined_iff a.p n
      Iff.intro (fun e => congrArg Int.ofNat (zero.mp e))
        (fun e => zero.mpr (Int.ofNat_inj.mp e)))
    (fun n => Iff.intro
      (fun e => False.elim (Nat.succ_ne_zero n
        ((IntRatio.value_undefined_iff a.p.neg n.succ).mp e)))
      (fun e => False.elim (Int.negSucc_ne_zero n e))) a.q

private def scale (a : Coordinates) (k : Int) : Coordinates :=
  ⟨a.p.mul k, a.q.mul k⟩

private theorem scale_mul_left (a b : Coordinates) (k : Int) :
    Eq ((scale a k).mul b) (scale (a.mul b) k) :=
  Eq.map₂ Coordinates.mk
    ((Eq.map₂ Int.add (Int.mul_right_comm a.p k b.q) (Int.mul_right_comm a.q k b.p)).trans
      (Int.add_mul (a.p.mul b.q) (a.q.mul b.p) k).symm)
    ((Eq.map₂ Int.sub (Int.mul_right_comm a.q k b.q) (Int.mul_right_comm a.p k b.p)).trans
      (Int.sub_mul (a.q.mul b.q) (a.p.mul b.p) k).symm)

private theorem scale_mul_right (a b : Coordinates) (k : Int) :
    Eq (a.mul (scale b k)) (scale (a.mul b) k) :=
  (a.mul_comm (scale b k)).trans
    ((scale_mul_left b a k).trans (congrArg (fun u => scale u k) (b.mul_comm a)))

private theorem chart_neg (p q : Int) :
    Eq (tangentChart ⟨p.neg, q.neg⟩) (tangentChart ⟨p, q⟩) :=
  let P := fun (q : Int) => Eq (tangentChart ⟨p.neg, q.neg⟩) (tangentChart ⟨p, q⟩)
  Int.rec (motive := P)
    (fun n => Nat.rec (motive := fun n => P (Int.ofNat n))
      (show Eq IntRatio.undefined IntRatio.undefined from Eq.refl)
      (fun k _ => congrArg (fun x => IntRatio.fraction x k) (Int.neg_neg p)) n)
    (fun _ => Eq.refl) q

private theorem chart_scale_positive (p q : Int) (k : Nat) :
    IntRatio.Equivalent (tangentChart (scale ⟨p, q⟩ (IntRatio.denominator k)))
      (tangentChart ⟨p, q⟩) :=
  let P := fun q => IntRatio.Equivalent
    (tangentChart (scale ⟨p, q⟩ (IntRatio.denominator k))) (tangentChart ⟨p, q⟩)
  Int.rec (motive := P)
    (fun n => IntRatio.value_scale p n k)
    (fun n =>
      Eq.subst (fun a => IntRatio.Equivalent
        (IntRatio.value a (n.succ.mul k.succ)) (IntRatio.value p.neg n.succ))
        (Int.neg_mul p (IntRatio.denominator k))
        (IntRatio.value_scale p.neg n.succ k)) q

private theorem chart_scale (a : Coordinates) (k : Int) (hk : Not (Eq k Int.zero)) :
    IntRatio.Equivalent (tangentChart (scale a k)) (tangentChart a) :=
  let P := fun k => Not (Eq k Int.zero) →
    IntRatio.Equivalent (tangentChart (scale a k)) (tangentChart a)
  (Int.rec (motive := P)
    (fun n => Nat.rec (motive := fun n => P (Int.ofNat n)) (fun h => False.elim (h Eq.refl))
      (fun n _ _ => chart_scale_positive a.p a.q n) n)
    (fun n _ =>
      let d := IntRatio.denominator n
      have flipped : Eq (scale a (Int.negSucc n)) ⟨(a.p.mul d).neg, (a.q.mul d).neg⟩ :=
        Eq.map₂ Coordinates.mk (Int.mul_neg a.p d) (Int.mul_neg a.q d)
      have charts := (congrArg tangentChart flipped).trans (chart_neg (a.p.mul d) (a.q.mul d))
      Eq.subst (fun x => IntRatio.Equivalent x (tangentChart a)) charts.symm
        (chart_scale_positive a.p a.q n)) k) hk

private theorem chart_mul_rescale (a b : Coordinates) (k l : Int)
    (hk : Not (Eq k Int.zero)) (hl : Not (Eq l Int.zero)) :
    IntRatio.Equivalent (tangentChart ((scale a k).mul (scale b l))) (tangentChart (a.mul b)) :=
  let remove := fun (x y : Coordinates) (f : Int) (h : Not (Eq f Int.zero)) =>
    Eq.subst (fun z => IntRatio.Equivalent (tangentChart z) (tangentChart (x.mul y)))
      (scale_mul_left x y f).symm (chart_scale (x.mul y) f h)
  (remove a (scale b l) k hk).trans
    (Eq.subst (fun z => IntRatio.Equivalent (tangentChart z) (tangentChart (a.mul b)))
      (scale_mul_right a b l).symm (chart_scale (a.mul b) l hl))

private theorem mul_neg_one (p : Int) : Eq (p.mul Int.one.neg) p.neg :=
  (Int.mul_neg p Int.one).trans (congrArg Int.neg (Int.mul_one p))

private theorem chart_representative (a : Coordinates) (h : Not (Eq a.q Int.zero)) :
    Exists fun (p : Int) => Exists fun (d : Nat) => Exists fun (k : Int) =>
      And (Not (Eq k Int.zero)) (And (Eq (tangentChart a) (IntRatio.fraction p d))
        (Eq (scale a k) ⟨p, IntRatio.denominator d⟩)) :=
  let P := fun q => Not (Eq q Int.zero) →
    Exists fun (p : Int) => Exists fun (d : Nat) => Exists fun (k : Int) =>
      And (Not (Eq k Int.zero)) (And (Eq (tangentChart ⟨a.p, q⟩) (IntRatio.fraction p d))
        (Eq (scale ⟨a.p, q⟩ k) ⟨p, IntRatio.denominator d⟩))
  (Int.rec (motive := P)
    (fun n => Nat.rec (motive := fun n => P (Int.ofNat n)) (fun h => False.elim (h Eq.refl))
      (fun d _ _ => Exists.intro a.p (Exists.intro d (Exists.intro Int.one
        (And.intro (Int.ofNat_succ_ne_zero Nat.zero)
          (And.intro Eq.refl
            (Eq.map₂ Coordinates.mk (Int.mul_one a.p) (Int.mul_one (IntRatio.denominator d)))))))) n)
    (fun d _ =>
      Exists.intro a.p.neg (Exists.intro d (Exists.intro Int.one.neg
        (And.intro (Int.negSucc_ne_zero Nat.zero)
          (And.intro Eq.refl (Eq.map₂ Coordinates.mk (mul_neg_one a.p) (mul_neg_one (Int.negSucc d)))))))) a.q) h

/-- When both inputs are finite, tangent addition is the chart of their homogeneous
product, including when that product reaches the pole. -/
theorem tangentAdd_chart (a b : Coordinates)
    (ha : Not (Eq a.q Int.zero)) (hb : Not (Eq b.q Int.zero)) :
    IntRatio.Equivalent (tangentAdd (tangentChart a) (tangentChart b)) (tangentChart (a.mul b)) :=
  (chart_representative a ha).elim (fun _ hp => hp.elim (fun _ hd => hd.elim (fun k hk =>
    (chart_representative b hb).elim (fun _ hr => hr.elim (fun _ he => he.elim (fun l hl =>
      have inputs := Eq.map₂ tangentAdd hk.right.left hl.right.left
      have product := Eq.map₂ (fun (x y : Coordinates) => tangentChart (x.mul y)) hk.right.right hl.right.right
      Eq.subst (fun x => IntRatio.Equivalent x (tangentChart (a.mul b)))
        (product.trans inputs.symm) (chart_mul_rescale a b k l hk.left hl.left)))))))

private theorem tangentAdd_congr_left {x y : IntRatio} (h : IntRatio.Equivalent x y)
    (z : IntRatio) : IntRatio.Equivalent (tangentAdd x z) (tangentAdd y z) :=
  let P := fun x y => IntRatio.Equivalent x y →
    IntRatio.Equivalent (tangentAdd x z) (tangentAdd y z)
  (IntRatio.rec (motive := fun x => P x y)
    (IntRatio.rec (motive := fun y => P IntRatio.undefined y)
      (fun _ => True.intro) (fun _ _ e => False.elim e) y)
    (fun p d => IntRatio.rec (motive := fun y => P (IntRatio.fraction p d) y)
      (fun e => False.elim e)
      (fun r e cross => IntRatio.rec (motive := fun z => IntRatio.Equivalent
        (tangentAdd (IntRatio.fraction p d) z) (tangentAdd (IntRatio.fraction r e) z))
        True.intro (fun t f =>
          let D := IntRatio.denominator d
          let E := IntRatio.denominator e
          let a := Coordinates.mk p D
          let b := Coordinates.mk r E
          let c := Coordinates.mk t (IntRatio.denominator f)
          have same : Eq (scale a E) (scale b D) := Eq.map₂ Coordinates.mk cross (Int.mul_comm D E)
          have scaledA := (chart_scale (a.mul c) E (Int.ofNat_succ_ne_zero e)).symm
          have scaledB := chart_scale (b.mul c) D (Int.ofNat_succ_ne_zero d)
          have middle := (scale_mul_left a c E).symm.trans
            ((congrArg (fun x : Coordinates => x.mul c) same).trans (scale_mul_left b c D))
          scaledA.trans (Eq.subst (fun x => IntRatio.Equivalent (tangentChart x) (tangentChart (b.mul c)))
            middle.symm scaledB)) z) y) x) h

private theorem tangentAdd_comm (x y : IntRatio) : Eq (tangentAdd x y) (tangentAdd y x) :=
  let P := fun x y => Eq (tangentAdd x y) (tangentAdd y x)
  IntRatio.rec (motive := fun x => P x y)
    (IntRatio.rec (motive := fun y => P IntRatio.undefined y) Eq.refl (fun _ _ => Eq.refl) y)
    (fun p d => IntRatio.rec (motive := fun y => P (IntRatio.fraction p d) y)
      Eq.refl (fun r e => congrArg tangentChart
        ((Coordinates.mk p (IntRatio.denominator d)).mul_comm
          (Coordinates.mk r (IntRatio.denominator e)))) y) x

theorem tangentAdd_congr {x x' y y' : IntRatio} (hx : IntRatio.Equivalent x x')
    (hy : IntRatio.Equivalent y y') :
    IntRatio.Equivalent (tangentAdd x y) (tangentAdd x' y') :=
  have middle := tangentAdd_congr_left hy x'
  have comm := Eq.map₂ IntRatio.Equivalent (tangentAdd_comm y x') (tangentAdd_comm y' x')
  (tangentAdd_congr_left hx y).trans (Eq.subst (fun p => p) comm middle)

theorem tangentSub_congr {x x' y y' : IntRatio} (hx : IntRatio.Equivalent x x')
    (hy : IntRatio.Equivalent y y') :
    IntRatio.Equivalent (tangentSub x y) (tangentSub x' y') :=
  tangentAdd_congr hx (IntRatio.neg_congr hy)

private theorem tangentAdd_assoc_fractions (p r t : Int) (d e f : Nat)
    (leftFinite : Not (Eq (tangentAdd (IntRatio.fraction p d) (IntRatio.fraction r e)) IntRatio.undefined))
    (rightFinite : Not (Eq (tangentAdd (IntRatio.fraction r e) (IntRatio.fraction t f)) IntRatio.undefined)) :
    IntRatio.Equivalent (tangentAdd (tangentAdd (IntRatio.fraction p d) (IntRatio.fraction r e))
      (IntRatio.fraction t f))
      (tangentAdd (IntRatio.fraction p d) (tangentAdd (IntRatio.fraction r e) (IntRatio.fraction t f))) :=
  let a := Coordinates.mk p (IntRatio.denominator d)
  let b := Coordinates.mk r (IntRatio.denominator e)
  let c := Coordinates.mk t (IntRatio.denominator f)
  have leftProduct := tangentAdd_chart (a.mul b) c
    (fun h => leftFinite ((tangentChart_undefined_iff (a.mul b)).mpr h)) (Int.ofNat_succ_ne_zero f)
  have rightProduct := tangentAdd_chart a (b.mul c) (Int.ofNat_succ_ne_zero d)
    (fun h => rightFinite ((tangentChart_undefined_iff (b.mul c)).mpr h))
  have same := congrArg tangentChart (Coordinates.mul_assoc a b c)
  (Eq.subst (fun x => IntRatio.Equivalent
    (tangentAdd (tangentChart (a.mul b)) (tangentChart c)) x) same leftProduct).trans rightProduct.symm

/-- Associativity holds when the two intermediate sums are finite.
If the common final product is at the pole, both sides are undefined. -/
theorem tangentAdd_assoc (x y z : IntRatio)
    (leftFinite : Not (Eq (tangentAdd x y) IntRatio.undefined))
    (rightFinite : Not (Eq (tangentAdd y z) IntRatio.undefined)) :
    IntRatio.Equivalent (tangentAdd (tangentAdd x y) z) (tangentAdd x (tangentAdd y z)) :=
  let P := fun x y z => Not (Eq (tangentAdd x y) IntRatio.undefined) →
    Not (Eq (tangentAdd y z) IntRatio.undefined) →
    IntRatio.Equivalent (tangentAdd (tangentAdd x y) z) (tangentAdd x (tangentAdd y z))
  (IntRatio.rec (motive := fun x => P x y z)
    (fun h _ => False.elim (h Eq.refl))
    (fun p d => IntRatio.rec (motive := fun y => P (IntRatio.fraction p d) y z)
      (fun h _ => False.elim (h Eq.refl))
      (fun r e => IntRatio.rec (motive := fun z => P (IntRatio.fraction p d) (IntRatio.fraction r e) z)
        (fun _ h => False.elim (h Eq.refl)) (fun t f => tangentAdd_assoc_fractions p r t d e f)
        z) y) x) leftFinite rightFinite

namespace MachinNumerals

def one : Nat := Nat.zero.succ
def two : Nat := one.succ
def three : Nat := two.succ
def five : Nat := three.succ.succ
def six : Nat := five.succ
def seven : Nat := six.succ
def eight : Nat := seven.succ
def nine : Nat := eight.succ
def ten : Nat := nine.succ

/-- Append a base-ten digit, also allowing a units term that carries. -/
def decimal (higher units : Nat) : Nat := (higher.mul ten).add units

def n12 : Nat := decimal one two
def n119 : Nat := decimal (decimal one one) nine
def n120 : Nat := decimal n12 Nat.zero
def n239 : Nat := decimal (decimal two three) nine

end MachinNumerals

open MachinNumerals

/-- The raw numerator and denominator of the last homogeneous product, 28561. -/
def machinDenominator : Nat := decimal (decimal (decimal (decimal two eight) five) six) one

/-- The input ratio 1/5. -/
def machinFifth : IntRatio := IntRatio.value Int.one five

/-- The reduced ratio 5/12 after the first doubling. -/
def machinTwofold : IntRatio := IntRatio.value (Int.ofNat five) n12

/-- The reduced ratio 120/119 after the second doubling. -/
def machinFourfold : IntRatio := IntRatio.value (Int.ofNat n120) n119

/-- The ratio 1/239 subtracted after the two doublings. -/
def machinCorrection : IntRatio := IntRatio.value Int.one n239

def machinChain : IntRatio :=
  let double := tangentAdd machinFifth machinFifth
  tangentSub (tangentAdd double double) machinCorrection

/-- First homogeneous doubling gives (10, 24), twice the pair (5, 12). -/
theorem machin_first_double_coordinates :
    Eq (projectiveMul Int.one (Int.ofNat five) Int.one (Int.ofNat five))
      ⟨Int.ofNat (five.mul two), Int.ofNat (n12.mul two)⟩ :=
  Eq.refl

theorem machin_first_double :
    IntRatio.Equivalent (tangentAdd machinFifth machinFifth) machinTwofold :=
  Eq.subst (fun a => IntRatio.Equivalent (tangentChart a) machinTwofold)
    machin_first_double_coordinates.symm (IntRatio.value_scale (Int.ofNat five) n12 one)

set_option maxRecDepth 2048 in
/-- Doubling the reduced first pair gives (120, 119) as it stands. -/
theorem machin_second_double_coordinates :
    Eq (projectiveMul (Int.ofNat five) (Int.ofNat n12) (Int.ofNat five) (Int.ofNat n12))
      ⟨Int.ofNat n120, Int.ofNat n119⟩ :=
  Eq.refl

theorem machin_second_double :
    Eq (tangentAdd machinTwofold machinTwofold) machinFourfold :=
  congrArg tangentChart machin_second_double_coordinates

/-- Each intermediate representative has an integer linear combination equal to one. -/
theorem machin_intermediate_bezout :
    And (Eq (((Int.ofNat five).mul (Int.ofNat five)).sub
      ((Int.ofNat two).mul (Int.ofNat n12))) Int.one)
      (Eq ((Int.ofNat n120).sub (Int.ofNat n119)) Int.one) :=
  And.intro Eq.refl Eq.refl

private theorem mul_decimal (a b c : Nat) :
    Eq (a.mul (decimal b c)) (decimal (a.mul b) (a.mul c)) :=
  (Nat.mul_add a (b.mul ten) c).trans
    (congrArg (fun r : Nat => r.add (a.mul c)) (Nat.mul_assoc a b ten).symm)

private theorem decimal_carry (a b c : Nat) :
    Eq (decimal a (decimal b c)) (decimal (a.add b) c) :=
  (Nat.add_assoc (a.mul ten) (b.mul ten) c).symm.trans
    (congrArg (fun r : Nat => r.add c) (Nat.add_mul a b ten).symm)

private theorem decimal_add (a b c d : Nat) :
    Eq ((decimal a b).add (decimal c d)) (decimal (a.add c) (b.add d)) :=
  (Nat.add_assoc (decimal a b) (c.mul ten) d).symm.trans
    ((congrArg (fun r : Nat => r.add d) (Nat.add_right_comm (a.mul ten) b (c.mul ten))).trans
      ((Nat.add_assoc ((a.mul ten).add (c.mul ten)) b d).trans
        (congrArg (fun r : Nat => r.add (b.add d)) (Nat.add_mul a c ten).symm)))

set_option maxRecDepth 4096 in
/-- Evaluate by decimal places to keep kernel reductions on small unary naturals. -/
private theorem machin_denominator_calc :
    Eq ((n119.mul n239).add n120) machinDenominator :=
  let n23 := decimal two three
  let n35 := decimal three five
  let n238 := decimal n23 eight
  let n273 := decimal (decimal two seven) three
  have hi : Eq (n119.mul n23) (decimal n273 seven) :=
    (mul_decimal n119 two three).trans
      ((Eq.map₂ decimal (show Eq (n119.mul two) n238 from Eq.refl)
        (show Eq (n119.mul three) (decimal n35 seven) from Eq.refl)).trans
        ((decimal_carry n238 n35 seven).trans
          (congrArg (fun r => decimal r seven) (show Eq (n238.add n35) n273 from Eq.refl))))
  let n99 := decimal nine nine
  have lo : Eq (n119.mul nine) (decimal (decimal ten seven) one) :=
    (Nat.mul_comm n119 nine).trans
      ((mul_decimal nine (decimal one one) nine).trans
        ((Eq.map₂ decimal (show Eq (nine.mul (decimal one one)) n99 from Eq.refl)
          (show Eq (nine.mul nine) (decimal eight one) from Eq.refl)).trans
          ((decimal_carry n99 eight one).trans
            (congrArg (fun r => decimal r one) (show Eq (n99.add eight) (decimal ten seven) from Eq.refl)))))
  let n2737 := decimal n273 seven
  let n107 := decimal ten seven
  have product : Eq (n119.mul n239) (decimal (n2737.add n107) one) :=
    (mul_decimal n119 n23 nine).trans ((Eq.map₂ decimal hi lo).trans (decimal_carry n2737 n107 one))
  have digits : Eq ((n2737.add n107).add n12) (decimal (decimal (decimal two eight) five) six) :=
    (congrArg (fun r : Nat => r.add n12) (decimal_add n273 seven ten seven)).trans
      ((decimal_add (n273.add ten) (seven.add seven) one two).trans
        ((decimal_carry ((n273.add ten).add one) one six).trans
          (congrArg (fun r => decimal r six)
            (show Eq (((n273.add ten).add one).add one) (decimal (decimal two eight) five) from Eq.refl))))
  (congrArg (fun r : Nat => r.add n120) product).trans
    ((Nat.add_right_comm ((n2737.add n107).mul ten) one n120).trans
      ((congrArg (fun r : Nat => r.add one) (Nat.add_mul (n2737.add n107) n12 ten).symm).trans
        (congrArg (fun r => decimal r one) digits)))

set_option maxRecDepth 4096 in
/-- Subtracting 1/239 from the fourfold pair gives (28561, 28561) before reduction. -/
theorem machin_raw_coordinates :
    Eq (projectiveMul (Int.ofNat n120) (Int.ofNat n119) Int.one.neg (Int.ofNat n239))
      ⟨Int.ofNat machinDenominator, Int.ofNat machinDenominator⟩ :=
  let cross := n119.mul n239
  have split : Eq (n120.mul n239) (machinDenominator.add n119) :=
    (Nat.succ_mul n119 n239).trans
      ((congrArg (Nat.add cross) (show Eq n239 (n120.add n119) from Eq.refl)).trans
        ((Nat.add_assoc cross n120 n119).symm.trans
          (congrArg (fun r : Nat => r.add n119) machin_denominator_calc)))
  have imaginary :=
    (congrArg (Int.ofNat (n120.mul n239)).add (mul_neg_one (Int.ofNat n119))).trans
      ((congrArg (fun r => (Int.ofNat r).sub (Int.ofNat n119)) split).trans
        ((Int.add_assoc (Int.ofNat machinDenominator) (Int.ofNat n119) (Int.ofNat n119).neg).trans
          ((congrArg (Int.ofNat machinDenominator).add (Int.add_right_neg (Int.ofNat n119))).trans
            (Int.add_zero (Int.ofNat machinDenominator)))))
  have real :=
    (congrArg (Int.ofNat cross).sub (mul_neg_one (Int.ofNat n120))).trans
      ((congrArg (Int.ofNat cross).add (Int.neg_neg (Int.ofNat n120))).trans
        (congrArg Int.ofNat machin_denominator_calc))
  Eq.map₂ Coordinates.mk imaginary real

theorem machin_raw :
    Eq (tangentSub machinFourfold machinCorrection)
      (IntRatio.value (Int.ofNat machinDenominator) machinDenominator) :=
  congrArg tangentChart machin_raw_coordinates

theorem machin_chain_to_raw :
    IntRatio.Equivalent machinChain (IntRatio.value (Int.ofNat machinDenominator) machinDenominator) :=
  let first := tangentAdd machinFifth machinFifth
  let four := tangentAdd first first
  have doubles := tangentAdd_congr machin_first_double machin_first_double
  have fourfold : IntRatio.Equivalent four machinFourfold :=
    Eq.subst (IntRatio.Equivalent four) machin_second_double doubles
  Eq.subst (IntRatio.Equivalent machinChain) machin_raw
    (tangentSub_congr fourfold (IntRatio.equivalent_refl machinCorrection))

theorem machin_chain_to_one :
    IntRatio.Equivalent machinChain (IntRatio.ofInt Int.one) :=
  machin_chain_to_raw.trans (IntRatio.value_self machinDenominator (Nat.succ_ne_zero _))

end Omega.Arithmetic
