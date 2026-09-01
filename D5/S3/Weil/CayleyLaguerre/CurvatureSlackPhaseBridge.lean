/- GID: D5/S3/Weil/CayleyLaguerre/CurvatureSlackPhaseBridge
   generality: G
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/CurvatureSlackPhaseBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Normalized dipole curvature and first Chebyshev slack retain reciprocal phase. -/

import D5.S3.Analytic.Adelic.OffLineCurvatureDipole
import D5.S3.Weil.CayleyLaguerre.ChebyshevSlackPositivity

/-!
# Curvature-slack phase bridge

The rational curvature profile of a reflected pair, after multiplication by
half of its positive denominator, is the compact coordinate used by the
Chebyshev slack bound.  At degree one, the squared coordinate and slack sum to
one.  Reciprocal inputs have the same slack and opposite coordinate signs.

Library-search audit trail (2026-09-02):

* Exact-name and whole-conclusion-shape searches found no frozen D5 theorem
  joining normalized curvature, degree-one Chebyshev slack, reciprocal
  invariance, and the two phase signs.
* `ChebyshevSlackPositivity.chebyshev_slack_bounds` owns the exact compact
  coordinate and slack shape, but only proves interval bounds and assumes the
  stronger scale condition `1 / 4 < a`.
* `OffLineCurvatureDipole.off_line_curvature_dipole` owns the constructed
  curvature and its rational formula; `off_line_curvature_eq_kappa` below
  consumes its first conjunct.
* Pinned Mathlib provides `Polynomial.Chebyshev.T_one` and
  `Polynomial.eval_X`. No pinned theorem states the reciprocal-coordinate
  identity `(a ^ 2 / x - a) / (a ^ 2 / x + a) = -(x - a) / (x + a)`.
-/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.CayleyLaguerre.CurvatureSlackPhaseBridge

/-- The first conjunct of the frozen curvature-dipole theorem is exactly the
compact-coordinate curvature formula at `x = (t - gamma)^2` and
`a = delta^2`. -/
theorem off_line_curvature_eq_kappa
    (delta gamma t : Real) (hdelta : 0 < delta) :
    let potential := fun u v : Real =>
      Real.log ((u - delta) ^ 2 + (v - gamma) ^ 2) / 2 +
        Real.log ((u + delta) ^ 2 + (v - gamma) ^ 2) / 2
    let curvature := fun v : Real => deriv (deriv (fun u => potential u v)) 0
    curvature t =
      2 * ((t - gamma) ^ 2 - delta ^ 2) /
        ((t - gamma) ^ 2 + delta ^ 2) ^ 2 := by
  dsimp only
  have hformula :=
    (D5.S3.Analytic.Adelic.OffLineCurvatureDipole.off_line_curvature_dipole
      delta gamma hdelta).1 t
  calc
    deriv
        (deriv fun u =>
          Real.log ((u - delta) ^ 2 + (t - gamma) ^ 2) / 2 +
            Real.log ((u + delta) ^ 2 + (t - gamma) ^ 2) / 2)
        0 =
        2 * (((t - gamma) ^ 2 - delta ^ 2) /
          ((t - gamma) ^ 2 + delta ^ 2) ^ 2) := hformula
    _ = 2 * ((t - gamma) ^ 2 - delta ^ 2) /
        ((t - gamma) ^ 2 + delta ^ 2) ^ 2 := by ring

/-- Positive compactification scale and nonnegative input identify normalized
dipole curvature with the compact coordinate. Degree-one Chebyshev slack is
its complementary square; reciprocal positive inputs preserve slack while
reversing the coordinate sign. -/
theorem curvature_slack_phase_bridge
    (a x : Real) (ha : 0 < a) (hx : 0 <= x) :
    let z := (x - a) / (x + a)
    let kappa := 2 * (x - a) / (x + a) ^ 2
    let slack := 1 -
      (Polynomial.Chebyshev.T Real (1 : Int)).eval z ^ 2
    ((x + a) * kappa / 2) ^ 2 + slack = 1 /\
      (x + a) * kappa / 2 = z /\
      (0 < x -> x < a ->
        (a ^ 2 / x - a) / (a ^ 2 / x + a) = -z /\
        1 - (Polynomial.Chebyshev.T Real (1 : Int)).eval
          ((a ^ 2 / x - a) / (a ^ 2 / x + a)) ^ 2 = slack /\
        z < 0 /\
        0 < (a ^ 2 / x - a) / (a ^ 2 / x + a)) := by
  dsimp only
  have hdenPositive : 0 < x + a := by linarith
  have hdenNe : x + a ≠ 0 := hdenPositive.ne'
  have hnormalized :
      (x + a) * (2 * (x - a) / (x + a) ^ 2) / 2 =
        (x - a) / (x + a) := by
    field_simp [hdenNe]
  refine ⟨?_, hnormalized, ?_⟩
  · rw [hnormalized, Polynomial.Chebyshev.T_one, Polynomial.eval_X]
    ring
  · intro hxPositive hxa
    have hxNe : x ≠ 0 := hxPositive.ne'
    have hyDenPositive : 0 < a ^ 2 / x + a := by positivity
    have hyDenNe : a ^ 2 / x + a ≠ 0 := hyDenPositive.ne'
    have hreciprocal :
        (a ^ 2 / x - a) / (a ^ 2 / x + a) =
          -((x - a) / (x + a)) := by
      field_simp [hxNe, hdenNe, hyDenNe, ha.ne']
      ring
    have hzNegative : (x - a) / (x + a) < 0 :=
      div_neg_of_neg_of_pos (sub_neg.mpr hxa) hdenPositive
    refine ⟨hreciprocal, ?_, hzNegative, ?_⟩
    · rw [hreciprocal]
      simp only [Polynomial.Chebyshev.T_one, Polynomial.eval_X]
      ring
    · rw [hreciprocal]
      exact neg_pos.mpr hzNegative

#print axioms off_line_curvature_eq_kappa
#print axioms curvature_slack_phase_bridge

end D5.S3.Weil.CayleyLaguerre.CurvatureSlackPhaseBridge
