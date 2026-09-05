/- GID: D5/S0/Asymptotics/Interference/BraggZeroFreeDisk
   generality: G
   mirror-B: D5/B/S0/Asymptotics/Interference/BraggZeroFreeDisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive peak and the Bernstein Lipschitz bound give a sharp zero-free disk. -/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/- Library-search audit trail (2026-09-04):
   * Keyword and symbol searches over D5 covered Bragg directions, zero-free
     disks and balls, peak lower bounds, Bernstein bounds, exponential sums,
     nonvanishing, and Lipschitz estimates in spaced, underscored, and CamelCase
     forms. The nearby finite-autocorrelation modules contain no local zero-free
     estimate.
   * The pzg-v170 digestion record and residual/digest indexes list this atom as
     residual-open with no coverage GID. The retired formalization-receipt tree
     is absent and was neither inspected nor recreated.
   * Generalized searches for norm-controlled nonvanishing and polynomial
     derivative bounds found Mathlib's reverse norm inequality, but no theorem
     packaging the explicit Bragg radius or its boundary sharpness witness.
   * Logs of every origin/lane/math branch above origin/dev contain no matching
     atom identifier, Bragg zero-free theorem, or equivalent in-flight result.
   * The source's displayed `|c_hat_m| / (e * phi * T) * (1 + o(1))` is
     asymptotic. The strict finite radius proved here is instead
     `|c_hat_m| / (e * (phi * T + 2))`; positivity assumptions exclude Lean's
     totalized-division degeneracies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S0.Asymptotics.Interference.BraggZeroFreeDisk

/-- The exact finite-radius denominator after combining the peak and Bernstein bounds. -/
def braggDenominator (T phi : ℝ) : ℝ :=
  Real.exp 1 * (phi * T + 2)

/-- The zero-free radius before replacing the finite `+ 2` term asymptotically. -/
def braggRadius (T phi coefficient : ℝ) : ℝ :=
  coefficient / braggDenominator T phi

/-- The local Lipschitz constant produced by the Bernstein estimate. -/
def braggSlope (T phi : ℝ) : ℝ :=
  T * braggDenominator T phi

/-- A linear peak profile showing that the open-disk radius is sharp under only
the peak and Lipschitz hypotheses. -/
def boundaryPeakModel (T phi coefficient : ℝ) (z : ℂ) : ℂ :=
  (T * coefficient : ℝ) - (braggSlope T phi : ℝ) * z

/-- A peak of height at least `T * coefficient`, together with the Bernstein
Lipschitz estimate, excludes every zero from the explicit open disk. A linear
profile with the same peak and exact Lipschitz constant has a zero on the
boundary, so no larger uniform open radius follows from these hypotheses. -/
theorem bragg_zero_free_disk
    (P : ℂ -> ℂ) (center : ℂ) (T phi coefficient : ℝ)
    (hT : 0 < T) (hphi : 0 < phi) (hcoefficient : 0 < coefficient)
    (hpeak : T * coefficient <= ‖P center‖)
    (hBernstein : ∀ w, ‖P w - P center‖ <= braggSlope T phi * dist w center) :
    ((∀ w ∈ Metric.ball center (braggRadius T phi coefficient), P w ≠ 0) ∧
      center ∈ Metric.ball center (braggRadius T phi coefficient) ∧ P center ≠ 0) ∧
    ∃ Q : ℂ -> ℂ,
      ‖Q 0‖ = T * coefficient ∧
      (∀ w, ‖Q w - Q 0‖ = braggSlope T phi * dist w 0) ∧
      ∃ boundary,
        dist boundary 0 = braggRadius T phi coefficient ∧ Q boundary = 0 := by
  have hscale : 0 < phi * T + 2 := by positivity
  have hdenominator : 0 < braggDenominator T phi := by
    exact mul_pos (Real.exp_pos 1) hscale
  have hradius : 0 < braggRadius T phi coefficient :=
    div_pos hcoefficient hdenominator
  have hslope : 0 < braggSlope T phi := mul_pos hT hdenominator
  have hslope_radius :
      braggSlope T phi * braggRadius T phi coefficient = T * coefficient := by
    simp only [braggSlope, braggRadius]
    field_simp [ne_of_gt hdenominator]
  constructor
  · refine ⟨?_, Metric.mem_ball_self hradius, ?_⟩
    · intro w hw hzero
      have hdistance : dist w center < braggRadius T phi coefficient := hw
      have hvariation := hBernstein w
      rw [hzero, zero_sub, norm_neg] at hvariation
      have hstrict :
          braggSlope T phi * dist w center < T * coefficient := by
        rw [← hslope_radius]
        exact mul_lt_mul_of_pos_left hdistance hslope
      exact (not_lt_of_ge (hpeak.trans hvariation)) hstrict
    · apply norm_ne_zero_iff.mp
      exact ne_of_gt ((mul_pos hT hcoefficient).trans_le hpeak)
  · refine ⟨boundaryPeakModel T phi coefficient, ?_, ?_, ?_⟩
    · simp [boundaryPeakModel, abs_of_pos hT, abs_of_pos hcoefficient]
    · intro w
      calc
        ‖boundaryPeakModel T phi coefficient w -
            boundaryPeakModel T phi coefficient 0‖ =
            ‖-(braggSlope T phi : ℂ) * w‖ := by
              congr 1
              simp only [boundaryPeakModel, mul_zero, sub_zero]
              ring
        _ = braggSlope T phi * dist w 0 := by
          simp [abs_of_pos hslope]
    · refine ⟨(braggRadius T phi coefficient : ℂ), ?_, ?_⟩
      · simp [abs_of_pos hradius]
      · simp only [boundaryPeakModel]
        have hcast :
            (braggSlope T phi : ℂ) * (braggRadius T phi coefficient : ℂ) =
              (T * coefficient : ℂ) := by
          norm_cast
        rw [hcast]
        norm_cast
        exact sub_self (T * coefficient)

#print axioms bragg_zero_free_disk

end D5.S0.Asymptotics.Interference.BraggZeroFreeDisk
