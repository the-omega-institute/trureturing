/- GID: D5/S3/Analytic/GoldenTomography/FinitePositiveRationalCircleTomography
   generality: I
   mirror-B: D5/B/S3/Analytic/GoldenTomography/FinitePositiveRationalCircleTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Distinct positive rational scales give distinct complex golden circle nodes and admit exact finite moment and time tomography. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenRationalCirclePhaseInjectivity
import D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
import D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
Library-first audit:
* the positive-rational quotient-circle injectivity theorem supplies node
  separation;
* `FiniteVandermondeTomography` supplies exact finite moment reconstruction;
* `FiniteCrystalTimeFrequencyBridge` supplies the matching time-window result;
* Mathlib's canonical `AddCircle.toCircle` map embeds the unit additive circle
  into the complex unit circle.

This module closes exact finite reconstruction on quotient-circle nodes. It
makes no uniform conditioning or infinite-family claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.GoldenTomography.FinitePositiveRationalCircleTomography

open D5.S3.Observer.GoldenPrimeCircle.GoldenRationalCirclePhaseInjectivity
open D5.S3.Analytic.GoldenTomography.FiniteVandermondeTomography
open D5.S3.ObserverMemory.FourierFibers.FiniteCrystalTimeFrequencyBridge

/-- Complex unit-circle node associated with a positive rational golden scale
point. -/
def positiveRationalGoldenComplexNode
    (scale : PositiveRational) : ℂ :=
  (AddCircle.toCircle (positiveRationalGoldenCirclePoint scale) : Circle : ℂ)

/-- The complex quotient-circle node remains injective on positive rationals. -/
theorem positive_rational_golden_complex_node_injective :
    Function.Injective positiveRationalGoldenComplexNode := by
  intro left right hNode
  apply positive_rational_golden_circle_point_injective
  apply AddCircle.injective_toCircle one_ne_zero
  apply Subtype.ext
  exact hNode

/-- An injective finite family of positive rational scales gives pairwise
distinct complex golden circle nodes. -/
theorem finite_positive_rational_circle_nodes_injective
    {n : ℕ} (scales : Fin n → PositiveRational)
    (hScales : Function.Injective scales) :
    Function.Injective
      (fun index => positiveRationalGoldenComplexNode (scales index)) :=
  positive_rational_golden_complex_node_injective.comp hScales

/-- The first matching number of power moments reconstructs amplitudes placed
at distinct positive rational quotient-circle nodes. -/
theorem finite_positive_rational_circle_moments_injective
    {n : ℕ} (scales : Fin n → PositiveRational)
    (hScales : Function.Injective scales) :
    Function.Injective
      (finiteMomentReadout
        (fun index => positiveRationalGoldenComplexNode (scales index))) :=
  finite_moment_readout_injective
    (finite_positive_rational_circle_nodes_injective scales hScales)

/-- The first matching scalar time window reconstructs amplitudes placed at
distinct positive rational quotient-circle nodes. -/
theorem finite_positive_rational_circle_time_window_injective
    {n : ℕ} (scales : Fin n → PositiveRational)
    (hScales : Function.Injective scales) :
    Function.Injective
      (firstCrystalTimeWindow
        (fun index => positiveRationalGoldenComplexNode (scales index))) :=
  first_crystal_time_window_injective
    (finite_positive_rational_circle_nodes_injective scales hScales)

#print axioms positive_rational_golden_complex_node_injective
#print axioms finite_positive_rational_circle_nodes_injective
#print axioms finite_positive_rational_circle_moments_injective
#print axioms finite_positive_rational_circle_time_window_injective

end D5.S3.Analytic.GoldenTomography.FinitePositiveRationalCircleTomography
