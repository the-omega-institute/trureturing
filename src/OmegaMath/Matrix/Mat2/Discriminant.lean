/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
import all OmegaInit.Prelude
import all OmegaInit.Data.Int.Basic
public import OmegaMath.Algebra.QuadraticExt.Polynomial

/-!
Omega original.

The discriminant of the fixed-point equation of a two-by-two integer matrix.
-/

noncomputable section
@[expose] public section

namespace Omega.Matrix

/-- Discriminant of the quadratic with coefficients `c, d - a, -b`. -/
def fixedFormDiscriminant (a b c d : Int) : Int :=
  (d.sub a).square.add (((Int.ofNat Nat.one.succ.succ.succ).mul b).mul c)

set_option allowUnsafeReducibility true in
attribute [local semireducible] Omega.Nat.add in
/-- The fixed-form discriminant is the square of the trace minus four times the determinant. -/
theorem fixedFormDiscriminant_eq (a b c d : Int) :
    Eq (fixedFormDiscriminant a b c d)
      ((a.add d).square.sub ((Int.ofNat Nat.one.succ.succ.succ).mul ((a.mul d).sub (b.mul c)))) :=
  let vars := Polynomial.Variables.cons a (.cons b (.cons c (.cons d (Polynomial.Variables.nil intRing))))
  let four := Polynomial.Expr.two.add Polynomial.Expr.two
  let x := Polynomial.e0
  let y := Polynomial.e1
  let z := Polynomial.e2
  let t := Polynomial.e3
  Polynomial.prove intRing intRingLaws vars
    ((t.sub x).square.add ((four.mul y).mul z))
    ((x.add t).square.sub (four.mul ((x.mul t).sub (y.mul z)))) Omega.rfl

/-- At determinant minus one the discriminant is the square of the trace plus four. -/
theorem det_neg_one_fixedFormDiscriminant (a b c d : Int)
    (h : Eq ((a.mul d).sub (b.mul c)) Int.one.neg) :
    Eq (fixedFormDiscriminant a b c d)
      ((a.add d).square.add (Int.ofNat Nat.one.succ.succ.succ)) :=
  let four := Int.ofNat Nat.one.succ.succ.succ
  let traceSq := (a.add d).square
  have replaced := congrArg (fun x : Int => traceSq.sub (four.mul x)) h
  have negFour : Eq (four.mul Int.one.neg) four.neg :=
    (Int.mul_neg four Int.one).trans (congrArg Int.neg (Int.mul_one four))
  (fixedFormDiscriminant_eq a b c d).trans
    (replaced.trans ((congrArg traceSq.sub negFour).trans
      (Int.sub_eq_add_neg.trans (congrArg traceSq.add (Int.neg_neg four)))))

end Omega.Matrix
