/- GID: D5/S3/Analytic/GoldenTomography/FinitePositiveRationalGoldenTomography
   generality: I
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePositiveRationalGoldenTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct positive rational scales have distinct lifted golden coordinates and admit exact finite moment and time tomography. -/

import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
import D5.S3.Observer.GoldenCoding.PrimeGoldenScaleCoordinate
import D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge

/-!
Library-first audit:
* `goldenScaleCoordinate` supplies the existing lifted logarithmic coordinate.
* Finite moment and time reconstruction reuse the existing Vandermonde and
  crystal-time injectivity theorems.
* This owner works on the universal-cover coordinate. It does not claim
  injectivity of the quotient-circle phase or a quantitative separation bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FinitePositiveRationalGoldenTomography

open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
open D5.S3.CompletionDynamics.GoldenMobius.GoldenScaleHelix
open D5.S3.Observer.GoldenCoding.PrimeGoldenScaleCoordinate
open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge

/-- The lifted golden logarithmic node assigned to a rational scale. -/
def liftedGoldenRationalNode (scale : ℚ) : ℝ :=
  goldenScaleCoordinate (scale : ℝ)

/-- Positive rational scales have equal lifted golden coordinates exactly when
the scales themselves are equal. -/
theorem lifted_golden_rational_node_eq_iff
    {left right : ℚ} (hLeft : 0 < left) (hRight : 0 < right) :
    liftedGoldenRationalNode left = liftedGoldenRationalNode right ↔
      left = right := by
  constructor
  · intro hNode
    have hPeriod : goldenScalePeriod ≠ 0 :=
      ne_of_gt golden_scale_period_pos
    have hLog : Real.log (left : ℝ) = Real.log (right : ℝ) := by
      unfold liftedGoldenRationalNode goldenScaleCoordinate at hNode
      have hScaled := congrArg
        (fun value : ℝ => value * goldenScalePeriod) hNode
      simpa [hPeriod] using hScaled
    have hLeftReal : 0 < (left : ℝ) := by
      exact_mod_cast hLeft
    have hRightReal : 0 < (right : ℝ) := by
      exact_mod_cast hRight
    have hCast : (left : ℝ) = (right : ℝ) := by
      calc
        (left : ℝ) = Real.exp (Real.log (left : ℝ)) :=
          (Real.exp_log hLeftReal).symm
        _ = Real.exp (Real.log (right : ℝ)) := by rw [hLog]
        _ = (right : ℝ) := Real.exp_log hRightReal
    exact_mod_cast hCast
  · intro h
    subst right
    rfl

/-- A finite injective family of positive rational scales gives an injective
family of lifted golden nodes. -/
theorem lifted_golden_nodes_injective
    {n : ℕ} (scales : Fin n → ℚ)
    (hPositive : ∀ index, 0 < scales index)
    (hScales : Function.Injective scales) :
    Function.Injective
      (fun index => liftedGoldenRationalNode (scales index)) := by
  intro left right hNode
  apply hScales
  exact (lifted_golden_rational_node_eq_iff
    (hPositive left) (hPositive right)).mp hNode

/-- The first matching number of power moments reconstructs amplitudes placed
at distinct positive rational golden nodes. -/
theorem finite_positive_rational_golden_moments_injective
    {n : ℕ} (scales : Fin n → ℚ)
    (hPositive : ∀ index, 0 < scales index)
    (hScales : Function.Injective scales) :
    Function.Injective
      (finiteMomentReadout
        (fun index => liftedGoldenRationalNode (scales index))) :=
  finite_moment_readout_injective
    (lifted_golden_nodes_injective scales hPositive hScales)

/-- The first matching time window reconstructs amplitudes placed at distinct
positive rational golden nodes. -/
theorem finite_positive_rational_golden_time_window_injective
    {n : ℕ} (scales : Fin n → ℚ)
    (hPositive : ∀ index, 0 < scales index)
    (hScales : Function.Injective scales) :
    Function.Injective
      (firstCrystalTimeWindow
        (fun index => liftedGoldenRationalNode (scales index))) :=
  first_crystal_time_window_injective
    (lifted_golden_nodes_injective scales hPositive hScales)

#print axioms lifted_golden_rational_node_eq_iff
#print axioms lifted_golden_nodes_injective
#print axioms finite_positive_rational_golden_moments_injective
#print axioms finite_positive_rational_golden_time_window_injective

end D5.S3.Analytic.GoldenTomography.FinitePositiveRationalGoldenTomography
