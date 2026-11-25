/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Matrix.LagrangeSchur.Sequence
public import OmegaMath.Matrix.LagrangeSchur.Order
public import OmegaMath.Algebra.QuadraticExt.Polynomial

/-!
Omega original.

Lagrange's identity and Cauchy–Schwarz for finite integer and rational sequences.
-/

noncomputable section

@[expose] public section

namespace Omega.LagrangeSchur

variable {A : Type} {relation : A → A → Prop} (r : CommRingOps A relation)
variable (law : r.Laws)

def sumU2 (xs : Sequence (CoordinatePair A)) : A :=
  xs.sum r.zero r.add (fun p => r.square p.u)

def sumV2 (xs : Sequence (CoordinatePair A)) : A :=
  xs.sum r.zero r.add (fun p => r.square p.v)

def sumUV (xs : Sequence (CoordinatePair A)) : A :=
  xs.sum r.zero r.add (fun p => r.mul p.u p.v)

def gramDet (xs : Sequence (CoordinatePair A)) : A :=
  r.sub (r.mul (sumU2 r xs) (sumV2 r xs)) (r.square (sumUV r xs))

def minor (p q : CoordinatePair A) : A :=
  r.sub (r.mul p.u q.v) (r.mul q.u p.v)

def minorSquares (xs : Sequence (CoordinatePair A)) : A :=
  xs.sumPairs r.zero r.add (fun p q => r.square (minor r p q))

private def row (u v a b c : A) : A :=
  r.sub (r.add (r.mul (r.square u) b) (r.mul (r.square v) a))
    (r.mul (r.mul r.two (r.mul u v)) c)

open Polynomial

private def rowExpr (u v a b c : Expr) : Expr :=
  .sub (.add (.mul u.square b) (.mul v.square a)) (.mul (.mul .two (.mul u v)) c)

include law

private theorem row_zero (u v : A) : r.eqv (row r u v r.zero r.zero r.zero) r.zero :=
  prove r law (.cons u (.cons v (Variables.nil r))) (rowExpr e0 e1 .zero .zero .zero) .zero Eq.refl

private theorem row_at (p q : CoordinatePair A) :
    r.eqv (r.square (minor r p q)) (row r p.u p.v (r.square q.u) (r.square q.v) (r.mul q.u q.v)) :=
  let vars := Variables.cons p.u (.cons p.v (.cons q.u (.cons q.v (Variables.nil r))))
  let lhs := (Expr.sub (.mul e0 e3) (.mul e2 e1)).square
  prove r law vars lhs (rowExpr e0 e1 e2.square e3.square (.mul e2 e3)) Eq.refl

private theorem row_add (u v a b c d e f : A) :
    r.eqv (row r u v (r.add a d) (r.add b e) (r.add c f))
      (r.add (row r u v a b c) (row r u v d e f)) :=
  let tail := Variables.cons c (.cons d (.cons e (.cons f (Variables.nil r))))
  let vars := Variables.cons u (.cons v (.cons a (.cons b tail)))
  let lhs := rowExpr e0 e1 (.add e2 e5) (.add e3 e6) (.add e4 e7)
  let rhs := Expr.add (rowExpr e0 e1 e2 e3 e4) (rowExpr e0 e1 e5 e6 e7)
  prove r law vars lhs rhs Eq.refl

private theorem row_sum (p : CoordinatePair A) (xs : Sequence (CoordinatePair A)) :
    r.eqv (xs.sum r.zero r.add (fun q => r.square (minor r p q)))
      (row r p.u p.v (sumU2 r xs) (sumV2 r xs) (sumUV r xs)) :=
  let u := p.u
  let v := p.v
  Sequence.rec (motive := fun xs =>
    r.eqv (xs.sum r.zero r.add (fun q => r.square (minor r p q)))
      (row r u v (sumU2 r xs) (sumV2 r xs) (sumUV r xs)))
    (law.symm (row_zero r law u v))
    (fun qAt tail ih =>
      let q := qAt .false
      law.trans (law.add_congr (row_at r law p q) ih)
        (law.symm (row_add r law u v (r.square q.u) (r.square q.v) (r.mul q.u q.v)
          (sumU2 r tail) (sumV2 r tail) (sumUV r tail)))) xs

private theorem gram_cons (pAt : Bool → CoordinatePair A) (xs : Sequence (CoordinatePair A)) :
    r.eqv (gramDet r (.consFn pAt xs))
      (r.add (row r (pAt .false).u (pAt .false).v (sumU2 r xs) (sumV2 r xs) (sumUV r xs))
        (gramDet r xs)) :=
  let p := pAt .false
  let vars := Variables.cons p.u (.cons p.v (.cons (sumU2 r xs)
    (.cons (sumV2 r xs) (.cons (sumUV r xs) (Variables.nil r)))))
  let lhs := Expr.sub (.mul (.add e0.square e2) (.add e1.square e3))
    (Expr.square (.add (.mul e0 e1) e4))
  let rhs := Expr.add (rowExpr e0 e1 e2 e3 e4) (.sub (.mul e2 e3) e4.square)
  prove r law vars lhs rhs Eq.refl

/-- The Gram determinant is the sum of the squares of the minors indexed by `i < j`. -/
theorem lagrange_gram (xs : Sequence (CoordinatePair A)) :
    r.eqv (gramDet r xs) (minorSquares r xs) :=
  Sequence.rec (motive := fun xs => r.eqv (gramDet r xs) (minorSquares r xs))
    (prove r law (Variables.nil r) (.sub (.mul .zero .zero) (.square .zero)) .zero Eq.refl)
    (fun p tail ih =>
      law.trans (gram_cons r law p tail)
        (law.add_congr (law.symm (row_sum r law (p .false) tail)) ih)) xs

omit law

theorem int_cauchy_schwarz (xs : Sequence (CoordinatePair Int)) :
    (Int.square (sumUV intRing xs)).le ((sumU2 intRing xs).mul (sumV2 intRing xs)) :=
  have nonneg := Sequence.sum_pairs_closed intRing Int.NonNeg True.intro int_nonneg_add
    (fun p q => Int.square (minor intRing p q)) (fun p q => Int.square_nonneg (minor intRing p q)) xs
  Eq.subst Int.NonNeg (Eq.symm (lagrange_gram intRing intRingLaws xs)) nonneg

theorem rational_cauchy_schwarz (xs : Sequence (CoordinatePair FiniteRatio)) :
    (FiniteRatio.square (sumUV rationalRing xs)).Le
      ((sumU2 rationalRing xs).mul (sumV2 rationalRing xs)) :=
  let a := rationalRing.square (sumUV rationalRing xs)
  let b := rationalRing.mul (sumU2 rationalRing xs) (sumV2 rationalRing xs)
  let d := minorSquares rationalRing xs
  have nonneg : RatioNonneg d :=
    Sequence.sum_pairs_closed rationalRing RatioNonneg True.intro ratio_nonneg_add
      (fun p q => rationalRing.square (minor rationalRing p q))
      (fun p q => ratio_nonneg_square (minor rationalRing p q)) xs
  ratio_le_of_gap a b d (lagrange_gram rationalRing rationalRingLaws xs) nonneg

end Omega.LagrangeSchur
