/- GID: D5/S3/Weil/Budget/GroundStateZeroLocalization
   generality: I
   mirror-B: D5/B/S3/Weil/Budget/GroundStateZeroLocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Vague spectral convergence forces eventual transform zeros near every zero ordinate. -/

import D5.S3.Weil.ZetaAnalytic.RiemannPoissonDensity
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Topology.Order.OrderClosed

/- Library-search audit trail (2026-08-29):
   * D5 searches for ground-state zero localization, vague convergence,
     eventual transform zeros, and residual supports found no exact owner.
   * The frozen `ZeroData` and `zeroCountingMeasure` declarations are the
     canonical enumerated nontrivial-zero carrier and multiplicity-weighted
     real-ordinate measure, so this module imports them rather than defining
     another zero spectrum.
   * Pinned Mathlib has weak convergence only for finite measures and no named
     vague topology for locally finite measures. The public premise therefore
     exposes vague convergence by its compactly supported continuous-test
     formula on the source carrier.
   * Exact Mathlib hits `exists_contDiff_tsupport_subset`,
     `lintegral_pos_iff_support`, `Measure.le_sum`, and
     `Measure.nonempty_inter_support_of_pos` supply the bump, atomic mass,
     and support-localization steps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Budget.GroundStateZeroLocalization

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaAnalytic.RiemannPoissonDensity

/-- Suppose residual spectral measures converge vaguely to the canonical
multiplicity-weighted zero-ordinate measure, and every residual support lies
inside the corresponding ground-transform zero set. Every open neighborhood
of an enumerated zero ordinate then contains a ground-transform zero for all
sufficiently large indices. -/
theorem ground_state_zero_localization
    (zeros : ZeroData) (zeroIndex : Nat)
    (residual : Nat -> Measure Real)
    (groundTransform : Nat -> Real -> Complex)
    (neighborhood : Set Real) (neighborhoodOpen : IsOpen neighborhood)
    (ordinateInNeighborhood : (zeros.zero zeroIndex).im ∈ neighborhood)
    (supportOnZeros : ∀ j,
      (residual j).support ⊆ {xi | groundTransform j xi = 0})
    (vagueConvergence : ∀ test : Real -> Real,
      Continuous test -> HasCompactSupport test ->
      (∀ x, 0 <= test x) ->
      Tendsto
        (fun j => lintegral (residual j)
          (fun x => ENNReal.ofReal (test x)))
        atTop
        (nhds (lintegral (zeroCountingMeasure zeros)
          (fun x => ENNReal.ofReal (test x))))) :
    ∀ᶠ j in atTop,
      ({xi | groundTransform j xi = 0} ∩ neighborhood).Nonempty := by
  let ordinate : Real := (zeros.zero zeroIndex).im
  obtain ⟨test, testSupport, testCompact, testSmooth, testRange,
      testAtOrdinate⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤)
      (neighborhoodOpen.mem_nhds ordinateInNeighborhood)
  have testContinuous : Continuous test := testSmooth.continuous
  have testNonnegative : ∀ x, 0 <= test x := by
    intro x
    exact (testRange ⟨x, rfl⟩).1
  have testMeasurable : Measurable (fun x => ENNReal.ofReal (test x)) :=
    testContinuous.measurable.ennreal_ofReal
  have ordinateInTestSupport :
      ordinate ∈ Function.support (fun x => ENNReal.ofReal (test x)) := by
    change ENNReal.ofReal (test ordinate) ≠ 0
    rw [testAtOrdinate]
    norm_num
  have componentLe :
      (zeros.multiplicity zeroIndex : ENNReal) •
          Measure.dirac ordinate <= zeroCountingMeasure zeros := by
    unfold zeroCountingMeasure
    simpa [ordinate] using
      (Measure.le_sum
        (fun n => (zeros.multiplicity n : ENNReal) •
          Measure.dirac (zeros.zero n).im) zeroIndex)
  have componentAtOrdinate :
      ((zeros.multiplicity zeroIndex : ENNReal) •
          Measure.dirac ordinate) {ordinate} =
        (zeros.multiplicity zeroIndex : ENNReal) := by
    simp [Measure.smul_apply]
  have targetAtomLower :
      (zeros.multiplicity zeroIndex : ENNReal) <=
        zeroCountingMeasure zeros {ordinate} := by
    rw [← componentAtOrdinate]
    exact componentLe {ordinate}
  have multiplicityPositive :
      0 < (zeros.multiplicity zeroIndex : ENNReal) := by
    exact_mod_cast zeros.multiplicity_pos zeroIndex
  have targetAtomPositive :
      0 < zeroCountingMeasure zeros {ordinate} :=
    multiplicityPositive.trans_le targetAtomLower
  have targetTestSupportPositive :
      0 < zeroCountingMeasure zeros
        (Function.support (fun x => ENNReal.ofReal (test x))) := by
    exact targetAtomPositive.trans_le
      (measure_mono (singleton_subset_iff.mpr ordinateInTestSupport))
  have targetIntegralPositive :
      0 < lintegral (zeroCountingMeasure zeros)
        (fun x => ENNReal.ofReal (test x)) :=
    (lintegral_pos_iff_support testMeasurable).2 targetTestSupportPositive
  have eventuallyIntegralPositive :
      ∀ᶠ j in atTop,
        0 < lintegral (residual j)
          (fun x => ENNReal.ofReal (test x)) :=
    (vagueConvergence test testContinuous testCompact testNonnegative).eventually
      (Ioi_mem_nhds targetIntegralPositive)
  have testSupportSubsetNeighborhood :
      Function.support (fun x => ENNReal.ofReal (test x)) ⊆ neighborhood := by
    intro x xInSupport
    apply testSupport
    apply subset_tsupport
    change test x ≠ 0
    intro testZero
    apply xInSupport
    simp [testZero]
  filter_upwards [eventuallyIntegralPositive] with j residualIntegralPositive
  have residualTestSupportPositive :
      0 < residual j
        (Function.support (fun x => ENNReal.ofReal (test x))) :=
    (lintegral_pos_iff_support testMeasurable).1 residualIntegralPositive
  have residualNeighborhoodPositive : 0 < residual j neighborhood :=
    residualTestSupportPositive.trans_le
      (measure_mono testSupportSubsetNeighborhood)
  obtain ⟨xi, xiInNeighborhood, xiInSupport⟩ :=
    (residual j).nonempty_inter_support_of_pos residualNeighborhoodPositive
  exact ⟨xi, supportOnZeros j xiInSupport, xiInNeighborhood⟩

#print axioms ground_state_zero_localization

end D5.S3.Weil.Budget.GroundStateZeroLocalization
