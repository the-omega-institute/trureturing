/- GID: D5/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/QuadraticDiscriminant
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/TauCeti/Algebra/Polynomial/QuadraticDiscriminant
   mirror-E: none(waiver:external-source-adaptation)
   anchors: []
   utility: none
   digest: Pinned TauCeti real algebraic dependency for entire boundary recovery. -/

/- Source: TauCetiProject/TauCeti revision 1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/Algebra/Polynomial/QuadraticDiscriminant.lean.
Adaptation: ordinary D5 import routes; selected declarations retain their original proofs.
License: docs/reports/licenses/TauCeti-LICENSE.txt. Original copyright notices follow.
Retire each transplanted declaration when the actual pinned mathlib supplies an equivalent
statement, and replace its consumers by direct imports and applications of that pinned owner.
This adaptation contributes no independent mathematical novelty or escape credit. -/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.FieldTheory.Perfect
import D5.S3.Geometry.AlgebraicBoundary.TauCeti.Algebra.QuadraticDiscriminant

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Tactic

/-!
# Separability and splitting criteria for quadratic polynomials

Mathlib's `Mathlib/Algebra/QuadraticDiscriminant.lean` works with the *equation*
`a x² + b x + c = 0` and relates its solutions to `discrim a b c = b² - 4 a c`. This file reads
those facts back as statements about the *polynomial* `C a * X ^ 2 + C b * X + C c`. Wherever a
statement mentions the discriminant it uses Mathlib's `discrim` rather than its expansion, so
that Mathlib's discriminant API applies to it directly; the two criteria phrased by a root or by
an Artin-Schreier condition mention no discriminant at all.

Over an ordered commutative ring, `TauCeti.quadratic_pos_iff_of_discrim_neg` and
`TauCeti.quadratic_neg_iff_of_discrim_neg` identify the sign of a quadratic with negative
discriminant from its leading coefficient.

Over a field, with `a ≠ 0`:

* `Polynomial.separable_quadratic_iff_discrim_ne_zero`: separable exactly when `discrim a b c ≠ 0`;
* `Polynomial.splits_quadratic_iff_exists_root`: splits exactly when it has a root — the
  characteristic-free core the other two are read off from;
* `Polynomial.splits_quadratic_iff_isSquare`: away from characteristic two, splits exactly when
  `discrim a b c` is a square;
* `Polynomial.splits_quadratic_of_discrim_eq_zero`: over a perfect field, splits as soon as
  `discrim a b c = 0`;
* `Polynomial.exists_quadratic_eq_zero_and_two_mul_add_eq_zero_of_discrim_eq_zero`: over a perfect
  field, if `discrim a b c = 0` then some `x` is a root of the quadratic and of its derivative;
* `Polynomial.card_rootSet_quadratic_of_discrim_eq_zero`: if it splits and `discrim a b c = 0`, it
  has exactly one root;
* `Polynomial.splits_quadratic_iff_exists_artinSchreier_of_two_eq_zero`: in characteristic two,
  where the discriminant degenerates to `b²` (`discrim_eq_sq_of_two_eq_zero`) and the square-class
  criterion says nothing, splits exactly when the
  Artin-Schreier invariant `a c / b²` lies in the image of `z ↦ z² + z`, written division-free.
  Here `b ≠ 0` is also required, which by `separable_quadratic_iff_discrim_ne_zero` is separability.

Three statements need neither a field nor `a ≠ 0`, and are stated over a commutative (semi)ring:
`Polynomial.derivative_quadratic`, computing the derivative as `2 a X + b`; the Bézout-type
`Polynomial.sq_derivative_quadratic_sub_mul_eq_C_discrim`, `(P')² - 4 a P = C (discrim a b c)`; and
its consequence `Polynomial.separable_quadratic_of_isUnit_discrim`, that the quadratic is separable
whenever its discriminant is a unit. Over a field that last statement is one direction of
`Polynomial.separable_quadratic_iff_discrim_ne_zero`, in every characteristic.

The two splitting criteria are consumed by the node-polynomial criteria of
`TauCeti/AlgebraicGeometry/EllipticCurve/NodePolynomial.lean`, which advance
`TauCetiRoadmap/EllipticCurves/README.md` §Layer 5 (twists): whether the node polynomial of a
multiplicative reduction splits over the residue field is exactly whether that reduction is split.

Adapted from the FLT project (`ImperialCollegeLondon/FLT`,
`FLT/Mathlib/Algebra/Polynomial/QuadraticDiscriminant.lean` at the roadmap's pin `bc2fe8ff7396`,
FLT PR #1088, Apache 2.0). That file's own header reads `Authors: Kevin Buzzard, Claude`;
following this repository's convention for adapted material, the upstream authorship is credited
here rather than in the copyright header. Ported with the source's `@[expose]` dropped, and
without its companion `FLT/Mathlib/Algebra/Polynomial/Splits.lean`: that file's
`Splits.of_natDegree_le_two_of_isRoot` is superseded here by Mathlib's own
`Polynomial.Splits.of_natDegree_eq_two`, which the one consumer can use directly since it knows
the degree is exactly two.
-/

public section

namespace Polynomial

end Polynomial

namespace TauCeti

open _root_.Polynomial

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A quadratic with negative discriminant is positive at every argument exactly when its
leading coefficient is positive. -/
theorem quadratic_pos_iff_of_discrim_neg {a b c : R} (hd : discrim a b c < 0) (x : R) :
    0 < (C a * X ^ 2 + C b * X + C c).eval x ↔ 0 < a := by
  simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
  have ha0 : a ≠ 0 := by
    intro ha
    subst a
    simp only [discrim, zero_mul, mul_zero, sub_zero] at hd
    nlinarith [sq_nonneg b]
  have hsq : ∀ s : R, discrim a b c ≠ s ^ 2 := by
    intro s hs
    exact (not_le.mpr hd) (by rw [hs]; exact sq_nonneg s)
  have hne : a * x ^ 2 + b * x + c ≠ 0 := by
    simpa only [sq] using quadratic_ne_zero_of_discrim_ne_sq hsq x
  constructor
  · intro hx
    rcases lt_or_gt_of_ne ha0 with ha | ha
    · have hnonneg := nonneg_of_discrim_le_zero (a := -a) (b := -b) (c := -c)
        (by simpa only [neg_pos] using ha)
        (by simpa only [discrim_neg] using hd.le) x 1
      simp only [one_pow, mul_one] at hnonneg
      nlinarith
    · exact ha
  · intro ha
    have hnonneg := nonneg_of_discrim_le_zero ha hd.le x 1
    simp only [one_pow, mul_one] at hnonneg
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- With negative discriminant, a quadratic is negative everywhere exactly when its
leading coefficient is negative. -/
theorem quadratic_neg_iff_of_discrim_neg {a b c : R} (hd : discrim a b c < 0) (x : R) :
    (C a * X ^ 2 + C b * X + C c).eval x < 0 ↔ a < 0 := by
  have h := quadratic_pos_iff_of_discrim_neg (a := -a) (b := -b) (c := -c)
    (by simpa only [discrim_neg] using hd) x
  have heq : (C (-a) * X ^ 2 + C (-b) * X + C (-c)).eval x =
      -(C a * X ^ 2 + C b * X + C c).eval x := by
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  simpa only [heq, neg_pos] using h

end TauCeti

end
