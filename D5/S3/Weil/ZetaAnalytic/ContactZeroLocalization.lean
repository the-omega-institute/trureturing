/- GID: D5/S3/Weil/ZetaAnalytic/ContactZeroLocalization
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaAnalytic/ContactZeroLocalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite contact spectra localize positive atoms near zero ordinates. -/

import D5.S3.Weil.Budget.GroundStateZeroLocalization

/- Library-search audit trail (2026-08-29):
   * The D5 body-shape search for finite Dirac sums and transform-zero
     subtypes found the canonical `zeroCountingMeasure` target but no finite
     contact-spectrum construction or exact localization theorem.
   * `GroundStateZeroLocalization` proves that a neighborhood eventually
     contains some transform zero. It does not recover an indexed contact
     atom, so the present theorem proves the finite-sum bridge locally.
   * Exact Mathlib hits `lintegral_sum_measure`,
     `lintegral_smul_measure`, `lintegral_dirac`, and
     `Finset.sum_pos_iff` turn positivity of a finite residual integral into
     a positive indexed Dirac term. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaAnalytic.ContactZeroLocalization

open Filter Function MeasureTheory Set Topology
open scoped ENNReal
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaAnalytic.RiemannPoissonDensity

/-- Let each residual spectrum be constructed from finitely many signed
contact atoms, where the subtype records the corresponding transform-zero
equation. If these positive atomic measures converge vaguely to the canonical
multiplicity-weighted zero-ordinate measure, every open neighborhood of an
enumerated ordinate eventually contains an indexed atom of positive weight. -/
theorem contact_zero_localization
    (zeros : ZeroData) (zeroIndex : Nat)
    (contactCount : Nat -> Nat)
    (groundTransform : Nat -> Real -> Complex)
    (contactAtom : ∀ n, Fin (contactCount n) ->
      {xi : Real // groundTransform n xi = 0})
    (contactWeight : ∀ n, Fin (contactCount n) -> ENNReal)
    (neighborhood : Set Real) (neighborhoodOpen : IsOpen neighborhood)
    (ordinateInNeighborhood : (zeros.zero zeroIndex).im ∈ neighborhood)
    (vagueConvergence : ∀ test : Real -> Real,
      Continuous test -> HasCompactSupport test ->
      (∀ x, 0 <= test x) ->
      Tendsto
        (fun n => lintegral
          (Measure.sum fun j : Fin (contactCount n) =>
            contactWeight n j • Measure.dirac (contactAtom n j).1)
          (fun x => ENNReal.ofReal (test x)))
        atTop
        (nhds (lintegral (zeroCountingMeasure zeros)
          (fun x => ENNReal.ofReal (test x))))) :
    ∀ᶠ n in atTop, ∃ j : Fin (contactCount n),
      0 < contactWeight n j ∧ (contactAtom n j).1 ∈ neighborhood := by
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
  have targetAtomPositive : 0 < zeroCountingMeasure zeros {ordinate} :=
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
      ∀ᶠ n in atTop,
        0 < lintegral
          (Measure.sum fun j : Fin (contactCount n) =>
            contactWeight n j • Measure.dirac (contactAtom n j).1)
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
  filter_upwards [eventuallyIntegralPositive] with n residualIntegralPositive
  rw [lintegral_sum_measure] at residualIntegralPositive
  simp only [lintegral_smul_measure, smul_eq_mul, lintegral_dirac]
    at residualIntegralPositive
  rw [tsum_fintype] at residualIntegralPositive
  have positiveTerm : ∃ j : Fin (contactCount n),
      0 < contactWeight n j * ENNReal.ofReal (test (contactAtom n j).1) := by
    simpa only [Finset.sum_pos_iff, Finset.mem_univ, true_and] using
      residualIntegralPositive
  obtain ⟨j, termPositive⟩ := positiveTerm
  have weightPositive : 0 < contactWeight n j :=
    (ENNReal.mul_pos_iff.mp termPositive).1
  have testPositive : 0 < ENNReal.ofReal (test (contactAtom n j).1) :=
    (ENNReal.mul_pos_iff.mp termPositive).2
  refine ⟨j, weightPositive, testSupportSubsetNeighborhood ?_⟩
  change ENNReal.ofReal (test (contactAtom n j).1) ≠ 0
  exact ne_of_gt testPositive

#print axioms contact_zero_localization

end D5.S3.Weil.ZetaAnalytic.ContactZeroLocalization
