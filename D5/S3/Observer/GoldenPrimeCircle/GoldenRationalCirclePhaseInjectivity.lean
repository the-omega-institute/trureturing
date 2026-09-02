/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenRationalCirclePhaseInjectivity
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenPrimeCircle/GoldenRationalCirclePhaseInjectivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden scale-circle point is injective on positive rational
     scales despite whole-shell blindness on positive reals. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenSecondMagnusSampling
import D5.S3.Observer.GoldenCoding.GoldenRationalShellRigidity
import Mathlib

/-!
Library-first audit:
* `GoldenScaleCircle` owns the lifted logarithmic coordinate and its whole-shell
  translation law.
* `GoldenSecondMagnusSampling` owns the additive-circle point; no parallel phase
  or quotient map is introduced here.
* `GoldenRationalShellRigidity` owns the arithmetic obstruction saying that a
  nonzero rational cannot cross a nontrivial natural golden shell and remain
  rational.
* Mathlib supplies the additive-circle kernel characterization.

The conclusion is exact injectivity on positive rational scales. It gives no
uniform metric separation or stable finite-precision decoder.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenRationalCirclePhaseInjectivity

open D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle
open D5.S3.Observer.GoldenPrimeCircle.GoldenSecondMagnusSampling
open D5.S3.Observer.GoldenCoding.GoldenRationalShellRigidity

/-- Positive rational scales, kept as a typed observation domain. -/
abbrev PositiveRational := {scale : ℚ // 0 < scale}

/-- The existing golden scale-circle point restricted to positive rationals. -/
def positiveRationalGoldenCirclePoint
    (scale : PositiveRational) : AddCircle (1 : ℝ) :=
  goldenScaleCirclePoint (scale.1 : ℝ)

/-- The lifted golden coordinate is injective on the positive real axis. -/
theorem golden_scale_coordinate_injective_on_pos :
    Set.InjOn goldenScaleCoordinate (Set.Ioi (0 : ℝ)) := by
  intro left hLeft right hRight hCoordinate
  apply Real.log_injOn_pos hLeft hRight
  unfold goldenScaleCoordinate at hCoordinate
  field_simp [golden_scale_period_ne_zero] at hCoordinate
  exact hCoordinate

/-- Equality of golden scale-circle points forces equality of positive rational
scales. Whole-shell periodicity has no nontrivial rational collision. -/
theorem positive_rational_golden_circle_point_injective :
    Function.Injective positiveRationalGoldenCirclePoint := by
  intro left right hCircle
  apply Subtype.ext
  change
    (goldenScaleCoordinate (left.1 : ℝ) : AddCircle (1 : ℝ)) =
      (goldenScaleCoordinate (right.1 : ℝ) : AddCircle (1 : ℝ)) at hCircle
  have hZero :
      ((goldenScaleCoordinate (left.1 : ℝ) -
        goldenScaleCoordinate (right.1 : ℝ) : ℝ) :
        AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub]
    exact sub_eq_zero.mpr hCircle
  obtain ⟨shift, hShift⟩ :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hZero
  have hShiftReal :
      (shift : ℝ) =
        goldenScaleCoordinate (left.1 : ℝ) -
          goldenScaleCoordinate (right.1 : ℝ) := by
    simpa using hShift
  have hLeftPos : 0 < (left.1 : ℝ) := by
    exact_mod_cast left.2
  have hRightPos : 0 < (right.1 : ℝ) := by
    exact_mod_cast right.2
  cases shift with
  | ofNat shell =>
      change
        (shell : ℝ) =
          goldenScaleCoordinate (left.1 : ℝ) -
            goldenScaleCoordinate (right.1 : ℝ) at hShiftReal
      have hCoordinate :
          goldenScaleCoordinate (left.1 : ℝ) =
            goldenScaleCoordinate (right.1 : ℝ) + (shell : ℝ) := by
        linarith
      have hScaledPos :
          0 < (Real.goldenRatio ^ 2) ^ shell * (right.1 : ℝ) :=
        mul_pos (pow_pos (sq_pos_of_pos Real.goldenRatio_pos) shell) hRightPos
      have hRealCollision :
          (left.1 : ℝ) =
            (Real.goldenRatio ^ 2) ^ shell * (right.1 : ℝ) := by
        apply golden_scale_coordinate_injective_on_pos hLeftPos hScaledPos
        calc
          goldenScaleCoordinate (left.1 : ℝ) =
              goldenScaleCoordinate (right.1 : ℝ) + (shell : ℝ) := hCoordinate
          _ = goldenScaleCoordinate
                ((Real.goldenRatio ^ 2) ^ shell * (right.1 : ℝ)) :=
            (golden_scale_coordinate_phi_even_pow_mul shell hRightPos).symm
      exact
        (rational_shell_collision_rigidity
          (ne_of_gt right.2) hRealCollision).2
  | negSucc shell =>
      change
        (-((shell + 1 : ℕ) : ℝ)) =
          goldenScaleCoordinate (left.1 : ℝ) -
            goldenScaleCoordinate (right.1 : ℝ) at hShiftReal
      have hCoordinate :
          goldenScaleCoordinate (right.1 : ℝ) =
            goldenScaleCoordinate (left.1 : ℝ) + ((shell + 1 : ℕ) : ℝ) := by
        linarith
      have hScaledPos :
          0 < (Real.goldenRatio ^ 2) ^ (shell + 1) * (left.1 : ℝ) :=
        mul_pos (pow_pos (sq_pos_of_pos Real.goldenRatio_pos) (shell + 1)) hLeftPos
      have hRealCollision :
          (right.1 : ℝ) =
            (Real.goldenRatio ^ 2) ^ (shell + 1) * (left.1 : ℝ) := by
        apply golden_scale_coordinate_injective_on_pos hRightPos hScaledPos
        calc
          goldenScaleCoordinate (right.1 : ℝ) =
              goldenScaleCoordinate (left.1 : ℝ) + ((shell + 1 : ℕ) : ℝ) :=
            hCoordinate
          _ = goldenScaleCoordinate
                ((Real.goldenRatio ^ 2) ^ (shell + 1) * (left.1 : ℝ)) :=
            (golden_scale_coordinate_phi_even_pow_mul (shell + 1) hLeftPos).symm
      exact
        (rational_shell_collision_rigidity
          (ne_of_gt left.2) hRealCollision).2.symm

/-- Equality is characterized exactly by the quotient-circle readout. -/
theorem positive_rational_golden_circle_point_eq_iff
    {left right : PositiveRational} :
    positiveRationalGoldenCirclePoint left =
        positiveRationalGoldenCirclePoint right ↔
      left = right :=
  positive_rational_golden_circle_point_injective.eq_iff

#print axioms golden_scale_coordinate_injective_on_pos
#print axioms positive_rational_golden_circle_point_injective
#print axioms positive_rational_golden_circle_point_eq_iff

end D5.S3.Observer.GoldenPrimeCircle.GoldenRationalCirclePhaseInjectivity
