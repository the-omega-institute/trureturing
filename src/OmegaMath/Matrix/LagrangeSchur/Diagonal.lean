/-
Copyright (c) 2026 The Omega Institute. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
prelude
public import OmegaMath.Matrix.LagrangeSchur.Schur
public import OmegaMath.Matrix.LagrangeSchur.Sequence
public import OmegaMath.Algebra.QuadraticExt.Polynomial

/-!
Omega original.

Schur completion for an arbitrary finite diagonal block and simultaneous
attainment of the minimum when every pivot is positive.
-/

noncomputable section

@[expose] public section

namespace Omega.LagrangeSchur

/-- The coupling coefficient, diagonal pivot, and variable of one block coordinate. -/
structure DiagonalCoordinate where
  b : FiniteRatio
  c : FiniteRatio
  y : FiniteRatio

def diagonalPivotForm (x : FiniteRatio) (xs : Sequence DiagonalCoordinate) : FiniteRatio :=
  xs.sum rationalRing.zero rationalRing.add (fun p => pivotForm p.b p.c x p.y)

def diagonalCorrection (xs : Sequence DiagonalCoordinate) : FiniteRatio :=
  xs.sum rationalRing.zero rationalRing.add (fun p => schurCorrection p.b p.c)

def diagonalForm (a x : FiniteRatio) (xs : Sequence DiagonalCoordinate) : FiniteRatio :=
  (a.mul x.square).add (diagonalPivotForm x xs)

def diagonalValue (a x : FiniteRatio) (xs : Sequence DiagonalCoordinate) : FiniteRatio :=
  (a.sub (diagonalCorrection xs)).mul x.square

def diagonalSquares (x : FiniteRatio) (xs : Sequence DiagonalCoordinate) : FiniteRatio :=
  xs.sum rationalRing.zero rationalRing.add (fun p => schurSquare p.b p.c x p.y)

def diagonalMinPoint (x : FiniteRatio) (xs : Sequence DiagonalCoordinate) :
    Sequence DiagonalCoordinate :=
  xs.map (fun p => ⟨p.b, p.c, schurMinPoint p.b p.c x⟩)

open Polynomial

private theorem sum_neg {α : Type} (f : α → FiniteRatio) (xs : Sequence α) :
    FiniteRatio.Equivalent (xs.sum rationalRing.zero rationalRing.add (fun p => (f p).neg))
      (xs.sum rationalRing.zero rationalRing.add f).neg :=
  Sequence.rec (motive := fun xs =>
    FiniteRatio.Equivalent (xs.sum rationalRing.zero rationalRing.add (fun p => (f p).neg))
      (xs.sum rationalRing.zero rationalRing.add f).neg)
    (rationalRingLaws.symm rationalRingLaws.neg_zero)
    (fun pAt tail ih =>
      let p := pAt .false
      rationalRingLaws.trans (rationalRingLaws.add_congr (rationalRingLaws.refl ((f p).neg)) ih)
        (rationalRingLaws.symm (rationalRingLaws.neg_add (f p)
          (tail.sum rationalRing.zero rationalRing.add f)))) xs

private theorem diagonal_pivot_terms (x : FiniteRatio) (xs : Sequence DiagonalCoordinate)
    (hn : xs.All (fun p => Not (Eq p.c.num Int.zero))) :
    FiniteRatio.Equivalent (diagonalPivotForm x xs)
      (((diagonalCorrection xs).neg.mul x.square).add (diagonalSquares x xs)) :=
  let form := fun (p : DiagonalCoordinate) => pivotForm p.b p.c x p.y
  let corr := fun (p : DiagonalCoordinate) => schurCorrection p.b p.c
  let square := fun (p : DiagonalCoordinate) => schurSquare p.b p.c x p.y
  let weighted := fun p => (corr p).neg.mul x.square
  have points := Sequence.all_imp
    (fun p : DiagonalCoordinate => Not (Eq p.c.num Int.zero))
    (fun p => FiniteRatio.Equivalent (form p) ((weighted p).add (square p)))
    (fun p h => pivot_complete p.b p.c x p.y h) xs hn
  have factor := rationalRingLaws.trans
    (Sequence.sum_mul_right rationalRing rationalRingLaws (fun p => (corr p).neg) x.square xs)
    (rationalRingLaws.mul_congr (sum_neg corr xs) (rationalRingLaws.refl x.square))
  rationalRingLaws.trans (Sequence.sum_congr rationalRing rationalRingLaws form (fun p => (weighted p).add (square p)) xs points)
    (rationalRingLaws.trans (Sequence.sum_add rationalRing rationalRingLaws weighted square xs)
      (rationalRingLaws.add_congr factor (rationalRingLaws.refl (diagonalSquares x xs))))

/-- Complete the square in every coordinate of a diagonal block with nonzero pivots. -/
theorem diagonal_schur_complete (a x : FiniteRatio) (xs : Sequence DiagonalCoordinate)
    (hn : xs.All (fun p => Not (Eq p.c.num Int.zero))) :
    FiniteRatio.Equivalent (diagonalForm a x xs) ((diagonalValue a x xs).add (diagonalSquares x xs)) :=
  let correction := diagonalCorrection xs
  let leading := a.mul x.square
  let penalty := correction.neg.mul x.square
  let squares := diagonalSquares x xs
  let tail := diagonalPivotForm x xs
  have terms : FiniteRatio.Equivalent tail (penalty.add squares) :=
    diagonal_pivot_terms x xs hn
  have expand := rationalRingLaws.add_congr
    (a := leading) (b := leading) (c := tail) (d := penalty.add squares)
    (rationalRingLaws.refl leading) terms
  have factor := rationalRingLaws.symm (rationalRingLaws.add_mul a correction.neg x.square)
  have reassociate := rationalRingLaws.symm (rationalRingLaws.add_assoc leading penalty squares)
  have combine := rationalRingLaws.add_congr factor (rationalRingLaws.refl squares)
  rationalRingLaws.trans expand (rationalRingLaws.trans reassociate combine)

private theorem diagonal_form_at_min (a x : FiniteRatio) (xs : Sequence DiagonalCoordinate)
    (hn : xs.All (fun p => Not (Eq p.c.num Int.zero))) :
    FiniteRatio.Equivalent (diagonalForm a x (diagonalMinPoint x xs)) (diagonalValue a x xs) :=
  let min := fun (p : DiagonalCoordinate) => DiagonalCoordinate.mk p.b p.c (schurMinPoint p.b p.c x)
  let form := fun (p : DiagonalCoordinate) => pivotForm p.b p.c x p.y
  let corr := fun (p : DiagonalCoordinate) => schurCorrection p.b p.c
  let penalty := fun p => (corr p).neg.mul x.square
  let correction := xs.sum rationalRing.zero rationalRing.add corr
  have point (p : DiagonalCoordinate) (h : Not (Eq p.c.num Int.zero)) :
      FiniteRatio.Equivalent (form (min p)) (penalty p) :=
    have vanish := rationalRingLaws.add_congr (rationalRingLaws.refl (penalty p))
      (schur_square_at_min p.b p.c x)
    rationalRingLaws.trans (pivot_complete p.b p.c x (schurMinPoint p.b p.c x) h)
      (rationalRingLaws.trans vanish (rationalRingLaws.add_zero (penalty p)))
  have sums := rationalRingLaws.trans (Sequence.sum_map rationalRing rationalRingLaws min form xs)
    (rationalRingLaws.trans (Sequence.sum_congr rationalRing rationalRingLaws (fun p => form (min p)) penalty xs
      (Sequence.all_imp (fun p : DiagonalCoordinate => Not (Eq p.c.num Int.zero))
        (fun p => FiniteRatio.Equivalent (form (min p)) (penalty p)) point xs hn))
      (rationalRingLaws.trans (Sequence.sum_mul_right rationalRing rationalRingLaws (fun p => (corr p).neg) x.square xs)
        (rationalRingLaws.mul_congr (sum_neg corr xs) (rationalRingLaws.refl x.square))))
  let vars := Variables.cons a (.cons correction (.cons x (Variables.nil rationalRing)))
  rationalRingLaws.trans (rationalRingLaws.add_congr (rationalRingLaws.refl (a.mul x.square)) sums)
    (prove rationalRing rationalRingLaws vars (.add (.mul e0 e2.square) (.mul (.neg e1) e2.square))
      (.mul (.sub e0 e1) e2.square) Eq.refl)

/-- With positive pivots the residual bounds every choice of coordinates and
is attained at the simultaneous coordinatewise shifts. -/
theorem diagonal_schur_min (a x : FiniteRatio) (xs : Sequence DiagonalCoordinate)
    (hp : xs.All (fun p => FiniteRatio.zero.Lt p.c)) :
    And ((diagonalValue a x xs).Le (diagonalForm a x xs))
      (FiniteRatio.Equivalent (diagonalForm a x (diagonalMinPoint x xs)) (diagonalValue a x xs)) :=
  let m := diagonalValue a x xs
  let s := diagonalSquares x xs
  let term := fun (p : DiagonalCoordinate) => schurSquare p.b p.c x p.y
  let positive := fun (p : DiagonalCoordinate) => FiniteRatio.zero.Lt p.c
  have hn := Sequence.all_imp positive (fun p => Not (Eq p.c.num Int.zero))
    (fun p => ratio_positive_num_ne_zero p.c) xs hp
  have squares := Sequence.all_imp positive (fun p => RatioNonneg (term p))
    (fun p => schur_square_nonneg p.b p.c x p.y) xs hp
  have nonneg : RatioNonneg s :=
    Sequence.sum_closed rationalRing RatioNonneg True.intro ratio_nonneg_add term xs squares
  have subtract := rationalRingLaws.sub_congr (diagonal_schur_complete a x xs hn)
    (rationalRingLaws.refl m)
  have cancel := prove rationalRing rationalRingLaws (.cons m (.cons s (Variables.nil rationalRing)))
    (.sub (.add e0 e1) e0) e1 Eq.refl
  have gap := rationalRingLaws.trans subtract cancel
  And.intro (ratio_le_of_gap m (diagonalForm a x xs) s gap nonneg)
    (diagonal_form_at_min a x xs hn)

end Omega.LagrangeSchur
