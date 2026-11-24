/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Algebra.QuadraticExt.Ring

/-!
Omega original.

Nonnegativity and order for the sums of squares in the Gram and Schur identities.
-/

noncomputable section

@[expose] public section

namespace Omega.LagrangeSchur

theorem int_nonneg_add (a b : Int) (ha : Int.NonNeg a) (hb : Int.NonNeg b) :
    Int.NonNeg (a.add b) :=
  Int.rec (motive := fun a => Int.NonNeg a → Int.NonNeg (a.add b))
    (fun a _ => Int.rec (motive := fun b => Int.NonNeg b → Int.NonNeg ((Int.ofNat a).add b))
      (fun _ _ => True.intro) (fun _ h => False.elim h) b hb)
    (fun _ h => False.elim h) a ha

private theorem int_nonneg_mul (a b : Int) (ha : Int.NonNeg a) (hb : Int.NonNeg b) :
    Int.NonNeg (a.mul b) :=
  Int.rec (motive := fun a => Int.NonNeg a → Int.NonNeg (a.mul b))
    (fun a _ => Int.rec (motive := fun b => Int.NonNeg b → Int.NonNeg ((Int.ofNat a).mul b))
      (fun _ _ => True.intro) (fun _ h => False.elim h) b hb)
    (fun _ h => False.elim h) a ha

def RatioNonneg (x : FiniteRatio) : Prop := Int.NonNeg x.num

theorem ratio_nonneg_add (a b : FiniteRatio) (ha : RatioNonneg a) (hb : RatioNonneg b) :
    RatioNonneg (a.add b) :=
  int_nonneg_add _ _
    ((Int.nonneg_mul_ofNat_succ a.num b.denPred).mpr ha)
    ((Int.nonneg_mul_ofNat_succ b.num a.denPred).mpr hb)

theorem ratio_nonneg_mul (a b : FiniteRatio) (ha : RatioNonneg a) (hb : RatioNonneg b) :
    RatioNonneg (a.mul b) :=
  int_nonneg_mul a.num b.num ha hb

theorem ratio_nonneg_square (a : FiniteRatio) : RatioNonneg a.square :=
  Int.square_nonneg a.num

private theorem ratio_nonneg_congr {a b : FiniteRatio} (h : a.Equivalent b)
    (ha : RatioNonneg a) : RatioNonneg b :=
  (Int.nonneg_mul_ofNat_succ b.num a.denPred).mp
    (Eq.subst Int.NonNeg h ((Int.nonneg_mul_ofNat_succ a.num b.denPred).mpr ha))

theorem ratio_le_iff_nonneg_sub (a b : FiniteRatio) :
    Iff (a.Le b) (RatioNonneg (b.sub a)) :=
  let left := b.num.mul (IntRatio.denominator a.denPred)
  let d := IntRatio.denominator b.denPred
  have e := congrArg left.add (Int.neg_mul a.num d)
  Iff.intro (fun h => Eq.subst Int.NonNeg e.symm h) (fun h => Eq.subst Int.NonNeg e h)

theorem ratio_le_of_gap (a b d : FiniteRatio) (h : (b.sub a).Equivalent d)
    (hd : RatioNonneg d) : a.Le b :=
  (ratio_le_iff_nonneg_sub a b).mpr (ratio_nonneg_congr (rationalRingLaws.symm h) hd)

theorem ratio_positive_nonneg (a : FiniteRatio) (h : FiniteRatio.zero.Lt a) :
    RatioNonneg a :=
  let d := IntRatio.denominator a.denPred
  let p := a.num.mul Int.one
  have hz : Int.NonNeg (p.sub (Int.zero.mul d)) := h.left
  Eq.subst Int.NonNeg
    ((congrArg p.sub (Int.zero_mul d)).trans ((Int.add_zero p).trans (Int.mul_one a.num))) hz

theorem ratio_positive_num_ne_zero (a : FiniteRatio) (h : FiniteRatio.zero.Lt a) :
    Not (Eq a.num Int.zero) :=
  fun hn => h.right ((Int.zero_mul (IntRatio.denominator a.denPred)).trans
    ((congrArg (fun n : Int => n.mul Int.one) hn).trans (Int.zero_mul Int.one)).symm)

end Omega.LagrangeSchur
