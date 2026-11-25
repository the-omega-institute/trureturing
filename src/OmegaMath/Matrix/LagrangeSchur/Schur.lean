/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Matrix.LagrangeSchur.Order
public import OmegaMath.Algebra.QuadraticExt.Polynomial

/-!
Omega original.

Scalar Schur completion over finite signed ratios, with the attained minimum
for a positive pivot.
-/

noncomputable section

@[expose] public section

namespace Omega.LagrangeSchur

private def r := rationalRing

/-- The pivot contribution `2bxy + cy²` to the original form. -/
def pivotForm (b c x y : FiniteRatio) : FiniteRatio :=
  (((rationalRing.two.mul b).mul x).mul y).add (c.mul y.square)

/-- The shift `(b/c)x` for a nonzero pivot. -/
def schurShift (b c x : FiniteRatio) : FiniteRatio := (b.mul c.inv).mul x

/-- The correction `b²/c` for a nonzero pivot. -/
def schurCorrection (b c : FiniteRatio) : FiniteRatio := b.square.mul c.inv

def schurSquare (b c x y : FiniteRatio) : FiniteRatio := c.mul (y.add (schurShift b c x)).square

def scalarForm (a b c x y : FiniteRatio) : FiniteRatio := (a.mul x.square).add (pivotForm b c x y)

def schurValue (a b c x : FiniteRatio) : FiniteRatio := (a.sub (schurCorrection b c)).mul x.square

def schurMinPoint (b c x : FiniteRatio) : FiniteRatio := (schurShift b c x).neg

open Polynomial

private theorem mul_div_cancel (b c : FiniteRatio) (hc : Not (Eq c.num Int.zero)) :
    FiniteRatio.Equivalent (c.mul (b.mul c.inv)) b :=
  let vars := Variables.cons b (.cons c (.cons c.inv (Variables.nil r)))
  have commute := prove r rationalRingLaws vars
    (.mul e1 (.mul e0 e2)) (.mul e0 (.mul e1 e2)) Eq.refl
  have cancel := rationalRingLaws.mul_congr (rationalRingLaws.refl b) (c.mul_inv_cancel hc)
  rationalRingLaws.trans commute (rationalRingLaws.trans cancel (rationalRingLaws.mul_one b))

private theorem correction_eq (b c : FiniteRatio) (hc : Not (Eq c.num Int.zero)) :
    FiniteRatio.Equivalent (c.mul (b.mul c.inv).square) (schurCorrection b c) :=
  let k := b.mul c.inv
  let vars := Variables.cons b (.cons c (.cons c.inv (Variables.nil r)))
  rationalRingLaws.trans (rationalRingLaws.symm (rationalRingLaws.mul_assoc c k k))
    (rationalRingLaws.trans (rationalRingLaws.mul_congr (mul_div_cancel b c hc) (rationalRingLaws.refl k))
      (prove r rationalRingLaws vars (.mul e0 (.mul e0 e2)) (.mul e0.square e2) Eq.refl))

/-- The individual pivot term is a centered square plus its negative correction. -/
theorem pivot_complete (b c x y : FiniteRatio) (hc : Not (Eq c.num Int.zero)) :
    FiniteRatio.Equivalent (pivotForm b c x y)
      (((schurCorrection b c).neg.mul x.square).add (schurSquare b c x y)) :=
  let k := b.mul c.inv
  let vars := Variables.cons c (.cons k (.cons x (.cons y (Variables.nil r))))
  let lhs := Expr.add (.mul (.mul (.mul .two (.mul e0 e1)) e2) e3) (.mul e0 e3.square)
  let rhs := Expr.add (.mul (.neg (.mul e0 e1.square)) e2.square)
    (.mul e0 (.square (.add e3 (.mul e1 e2))))
  have twice := rationalRingLaws.mul_congr (rationalRingLaws.refl r.two)
    (rationalRingLaws.symm (mul_div_cancel b c hc))
  have cross := rationalRingLaws.mul_congr
    (rationalRingLaws.mul_congr twice (rationalRingLaws.refl x)) (rationalRingLaws.refl y)
  have replaceB := rationalRingLaws.add_congr cross (rationalRingLaws.refl (c.mul y.square))
  have correction := rationalRingLaws.mul_congr
    (rationalRingLaws.neg_congr (correction_eq b c hc)) (rationalRingLaws.refl x.square)
  have replaceCorrection := rationalRingLaws.add_congr correction
    (rationalRingLaws.refl (schurSquare b c x y))
  have expand := prove r rationalRingLaws vars lhs rhs Eq.refl
  rationalRingLaws.trans replaceB (rationalRingLaws.trans expand replaceCorrection)

/-- Complete the square for every finite, nonzero pivot `c`. -/
theorem scalar_schur_complete (a b c x y : FiniteRatio) (hc : Not (Eq c.num Int.zero)) :
    FiniteRatio.Equivalent (scalarForm a b c x y)
      ((schurValue a b c x).add (schurSquare b c x y)) :=
  let vars := Variables.cons a (.cons (schurCorrection b c) (.cons x
    (.cons (schurSquare b c x y) (Variables.nil r))))
  let lhs := Expr.add (.mul e0 e2.square) (.add (.mul (.neg e1) e2.square) e3)
  let rhs := Expr.add (.mul (.sub e0 e1) e2.square) e3
  have complete := rationalRingLaws.add_congr (rationalRingLaws.refl (a.mul x.square))
    (pivot_complete b c x y hc)
  rationalRingLaws.trans complete (prove r rationalRingLaws vars lhs rhs Eq.refl)

theorem schur_square_at_min (b c x : FiniteRatio) :
    FiniteRatio.Equivalent (schurSquare b c x (schurMinPoint b c x)) FiniteRatio.zero :=
  let vars := Variables.cons c (.cons (schurShift b c x) (Variables.nil r))
  prove r rationalRingLaws vars (.mul e0 (.square (.add (.neg e1) e1))) .zero Eq.refl

theorem schur_square_nonneg (b c x y : FiniteRatio) (hc : FiniteRatio.zero.Lt c) :
    RatioNonneg (schurSquare b c x y) :=
  ratio_nonneg_mul c _ (ratio_positive_nonneg c hc)
    (ratio_nonneg_square (y.add (schurShift b c x)))

/-- For a positive pivot, the residual is a lower bound attained at `y = -(b/c)x`. -/
theorem scalar_schur_min (a b c x : FiniteRatio) (hc : FiniteRatio.zero.Lt c) :
    And (∀ y : FiniteRatio, (schurValue a b c x).Le (scalarForm a b c x y))
      (FiniteRatio.Equivalent (scalarForm a b c x (schurMinPoint b c x)) (schurValue a b c x)) :=
  let m := schurValue a b c x
  let y₀ := schurMinPoint b c x
  have hn := ratio_positive_num_ne_zero c hc
  And.intro
    (fun y =>
      let s := schurSquare b c x y
      have subtract := rationalRingLaws.sub_congr
        (scalar_schur_complete a b c x y hn) (rationalRingLaws.refl m)
      have cancel := prove r rationalRingLaws (.cons m (.cons s (Variables.nil r)))
        (.sub (.add e0 e1) e0) e1 Eq.refl
      ratio_le_of_gap m (scalarForm a b c x y) s
        (rationalRingLaws.trans subtract cancel) (schur_square_nonneg b c x y hc))
    (have vanish := rationalRingLaws.add_congr (rationalRingLaws.refl m) (schur_square_at_min b c x)
     rationalRingLaws.trans (scalar_schur_complete a b c x y₀ hn)
       (rationalRingLaws.trans vanish (rationalRingLaws.add_zero m)))

end Omega.LagrangeSchur
