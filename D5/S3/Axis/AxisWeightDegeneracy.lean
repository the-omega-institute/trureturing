/- GID: D5/S3/Axis/AxisWeightDegeneracy
   generality: I
   mirror-B: D5/B/S3/Axis/AxisWeightDegeneracy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Consecutive axis weights coincide exactly on the diagonal x = y. -/

import D5.S3.Axis.AxisTraceRecurrence

namespace D5.S3.Axis.AxisWeightDegeneracy

open Real
open D5.S3.Axis.AxisTraceRecurrence

/- Errata note. The docstring attached to `AxisTraceRecurrence.axisWeight_zero` asserts that
   "the recurrence never degenerates: no depth carries the same weight as its successor
   unless the reading is trivial". That sentence is false, and it is not what the theorem it
   is attached to proves — that theorem only evaluates the weight at depth zero. Degeneracy
   at the first step happens on a whole line of readings, `x = y`, and `x = y = 1` is not a
   trivial reading. The frozen module is left byte-identical; the correction is carried here
   as a stronger statement that names the exact degeneracy locus. -/

/-- Both the golden ratio and its conjugate drop their square by exactly one unit of
themselves, which is why the first weight step compares `-x + y` against zero. -/
theorem sq_sub_self : goldenRatio ^ 2 - goldenRatio = 1 ∧ goldenConj ^ 2 - goldenConj = 1 := by
  constructor
  · have h : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
    linarith
  · have h : goldenConj ^ 2 = goldenConj + 1 := goldenConj_sq
    linarith

/-- Consecutive axis weights at the bottom of the tower coincide exactly on `x = y`. -/
theorem axisWeight_zero_eq_one_iff (x y : ℝ) :
    axisWeight x y 0 = axisWeight x y 1 ↔ x = y := by
  have hphi : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  have hpsi : goldenConj ^ 2 = goldenConj + 1 := goldenConj_sq
  have hone : axisWeight x y 1
      = Real.exp (-x * (goldenRatio + 1) + y * (goldenConj + 1)) := by
    change Real.exp (-x * goldenRatio ^ (1 + 1) + y * goldenConj ^ (1 + 1)) = _
    rw [show (1 : ℕ) + 1 = 2 from rfl, hphi, hpsi]
  rw [axisWeight_zero x y, hone, Real.exp_eq_exp]
  constructor
  · intro h
    linarith
  · intro h
    subst h
    ring

/-- The claim the frozen docstring makes is false, witnessed at `x = y = 1`. -/
theorem degeneracy_occurs_off_the_trivial_reading :
    axisWeight 1 1 0 = axisWeight 1 1 1 :=
  (axisWeight_zero_eq_one_iff 1 1).mpr rfl

/-- Degeneracy is not universal either: off the diagonal the two weights differ. -/
theorem axisWeight_zero_ne_one_off_diagonal (x y : ℝ) (h : x ≠ y) :
    axisWeight x y 0 ≠ axisWeight x y 1 := fun hEq =>
  h ((axisWeight_zero_eq_one_iff x y).mp hEq)

/-- The degeneracy locus packaged: the first weight step degenerates exactly on `x = y`, it
does occur at a reading that is not trivial, and it fails off that line. -/
theorem axis_weight_degeneracy_locus_package :
    (∀ x y : ℝ, axisWeight x y 0 = axisWeight x y 1 ↔ x = y) ∧
      axisWeight 1 1 0 = axisWeight 1 1 1 ∧
        ∀ x y : ℝ, x ≠ y → axisWeight x y 0 ≠ axisWeight x y 1 :=
  ⟨axisWeight_zero_eq_one_iff, degeneracy_occurs_off_the_trivial_reading,
    axisWeight_zero_ne_one_off_diagonal⟩

end D5.S3.Axis.AxisWeightDegeneracy
