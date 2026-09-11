/- GID: D5/S3/Observer/Fluctuation/ThermalCoefficientFloor
   generality: G
   mirror-B: D5/B/S3/Observer/Fluctuation/ThermalCoefficientFloor
   mirror-E: none(waiver:symbolic-analysis-no-numerical-evidence)
   anchors: []
   utility: none
   digest: The thermal response coefficient is bounded below by the inverse temperature alone. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The source packages two lower bounds under one hypothesis: a common positive
floor on every mode frequency. Only the second bound uses that floor; its
coefficient carries the floor explicitly. The first bound's right-hand side is
the inverse temperature alone, and its proof needs no common floor at all,
only that each individual frequency is positive.

This module isolates the first bound under that weaker hypothesis. The escape
content is the hyperbolic monotonicity estimate below, which the pinned
library does not carry: a search of the hyperbolic files found no coth at all
and no inequality of this shape.

The equilibrium preparation that identifies a physical fluctuation with this
spectral sum is not formalized here. What is proved is the coefficient
inequality; reading it as a statement about a prepared thermal state requires
that preparation as a separate hypothesis.
-/

namespace D5.S3.Observer.Fluctuation.ThermalCoefficientFloor

open Real Set

noncomputable section

/-- The escape content: on the nonnegative axis the hyperbolic sine never
exceeds its argument times the hyperbolic cosine. The difference vanishes at
the origin and has derivative `x * sinh x`, which is nonnegative there. -/
theorem sinh_le_self_mul_cosh_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.sinh x ≤ x * Real.cosh x := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun z : ℝ => z * Real.cosh z - Real.sinh z)
      (y * Real.sinh y) y := by
    intro y
    have hmul : HasDerivAt (fun z : ℝ => z * Real.cosh z)
        (1 * Real.cosh y + y * Real.sinh y) y :=
      (hasDerivAt_id y).mul (Real.hasDerivAt_cosh y)
    have h := hmul.sub (Real.hasDerivAt_sinh y)
    have heq : 1 * Real.cosh y + y * Real.sinh y - Real.cosh y = y * Real.sinh y := by ring
    rwa [heq] at h
  have hmono : MonotoneOn (fun z : ℝ => z * Real.cosh z - Real.sinh z) (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => ((hderiv y).continuousAt).continuousWithinAt)
      (fun y _ => (hderiv y).differentiableAt.differentiableWithinAt) ?_
    intro y hy
    rw [interior_Ici] at hy
    rw [(hderiv y).deriv]
    exact mul_nonneg (le_of_lt hy) (Real.sinh_nonneg_iff.mpr (le_of_lt hy))
  have hstep := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp only [zero_mul, Real.sinh_zero, sub_zero] at hstep
  linarith

/-- The hyperbolic cotangent, which the pinned library does not define. -/
def coth (x : ℝ) : ℝ := Real.cosh x / Real.sinh x

/-- Companion: the argument times its hyperbolic cotangent is at least one. -/
theorem one_le_self_mul_coth {x : ℝ} (hx : 0 < x) : 1 ≤ x * coth x := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have hkey : Real.sinh x ≤ x * Real.cosh x := sinh_le_self_mul_cosh_of_nonneg hx.le
  rw [coth, mul_div_assoc', le_div_iff₀ hs, one_mul]
  exact hkey

/-- Companion: the cotangent dominates the reciprocal of its argument. -/
theorem inv_le_coth {x : ℝ} (hx : 0 < x) : x⁻¹ ≤ coth x := by
  have h := one_le_self_mul_coth hx
  rw [inv_le_iff_one_le_mul₀ hx]
  linarith [h, mul_comm x (coth x)]

/-- The thermal coefficient is bounded below by the inverse temperature, with
no common positive floor on the frequencies: each frequency being positive in
its own right already suffices. -/
theorem inv_le_thermal_coefficient {beta hbar nu : ℝ}
    (hbeta : 0 < beta) (hhbar : 0 < hbar) (hnu : 0 < nu) :
    beta⁻¹ ≤ (hbar * nu / 2) * coth (beta * hbar * nu / 2) := by
  have hx : 0 < beta * hbar * nu / 2 := by positivity
  have hcoth := inv_le_coth hx
  have hcoef : (0:ℝ) < hbar * nu / 2 := by positivity
  have hstep : (hbar * nu / 2) * (beta * hbar * nu / 2)⁻¹
      ≤ (hbar * nu / 2) * coth (beta * hbar * nu / 2) :=
    mul_le_mul_of_nonneg_left hcoth hcoef.le
  have hval : (hbar * nu / 2) * (beta * hbar * nu / 2)⁻¹ = beta⁻¹ := by
    field_simp
  linarith [hval ▸ hstep]

/-- The finite spectral form. Every mode contributes its own positive
frequency and a nonnegative weight; the sum is bounded below by the inverse
temperature times the static response, and no frequency floor appears. -/
theorem inv_mul_sum_le_thermal_sum {iota : Type*} [Fintype iota]
    (beta hbar : ℝ) (nu w : iota → ℝ)
    (hbeta : 0 < beta) (hhbar : 0 < hbar)
    (hnu : ∀ a, 0 < nu a) (hw : ∀ a, 0 ≤ w a) :
    beta⁻¹ * ∑ a, w a / (nu a) ^ 2
      ≤ ∑ a, ((hbar * nu a / 2) * coth (beta * hbar * nu a / 2)) * (w a / (nu a) ^ 2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro a _
  have hweight : 0 ≤ w a / (nu a) ^ 2 :=
    div_nonneg (hw a) (by positivity)
  exact mul_le_mul_of_nonneg_right
    (inv_le_thermal_coefficient hbeta hhbar (hnu a)) hweight

#print axioms sinh_le_self_mul_cosh_of_nonneg
#print axioms inv_le_thermal_coefficient
#print axioms inv_mul_sum_le_thermal_sum

end
end D5.S3.Observer.Fluctuation.ThermalCoefficientFloor
