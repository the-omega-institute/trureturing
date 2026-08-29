/- GID: D5/S3/Analytic/Adelic/ToroidalInnerThresholdIdentity
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/ToroidalInnerThresholdIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Toroidal escape and innerness thresholds coincide at the critical line. -/

import D5.S3.Analytic.Adelic.ToroidalCommonZeroLocus
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-29):
   * Repository searches for toroidal and eventual-innerness thresholds found
     no exact D5 statement owner. `ToroidalCommonZeroLocus` is the canonical
     common-kernel constituent and is applied pointwise below.
   * The similarly named frozen `BodeWidthCriterion` concerns a finite
     scattering pulse and does not own either source threshold.
   * Pinned Mathlib supplies the exact order bridge
     `csInf_upperBounds_eq_csSup`; it is applied directly. Mathlib has no
     completed-zeta eventual-innerness theorem. No new definition or
     alternate carrier is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.ToroidalInnerThresholdIdentity

open Set
open D5.S3.Zeros.CompletedZeta
open D5.S3.Analytic.Adelic.ToroidalCommonZeroLocus

/-- The supremal right-half-plane deviation of the common toroidal kernel is
the infimal eventual-innerness threshold. Both thresholds vanish exactly when
every completed-zeta zero lies on the critical line. -/
theorem toroidal_inner_threshold_identity {Index : Type*}
    (period twist : Index -> ℂ -> ℂ) (innerAt : ℝ -> Prop)
    (factorization : ∀ index point,
      period index point = xiReading point * twist index point)
    (pointwiseNonvanishing : ∀ point, ∃ index, twist index point ≠ 0)
    (suzukiEquivalence : ∀ a : ℝ, 0 ≤ a ->
      ((∀ omega : ℝ, a < omega -> innerAt omega) ↔
        ∀ point : ℂ, xiReading point = 0 ->
          point.re ≤ (1 : ℝ) / 2 + a))
    (deviationNonempty :
      Set.Nonempty {a : ℝ | ∃ point : ℂ,
        (1 : ℝ) / 2 ≤ point.re ∧
        (∀ index, period index point = 0) ∧
        a = point.re - (1 : ℝ) / 2})
    (deviationBounded :
      BddAbove {a : ℝ | ∃ point : ℂ,
        (1 : ℝ) / 2 ≤ point.re ∧
        (∀ index, period index point = 0) ∧
        a = point.re - (1 : ℝ) / 2}) :
    let deviations : Set ℝ := {a | ∃ point : ℂ,
      (1 : ℝ) / 2 ≤ point.re ∧
      (∀ index, period index point = 0) ∧
      a = point.re - (1 : ℝ) / 2}
    let toroidalThreshold := sSup deviations
    let innerCandidates : Set ℝ :=
      {a | 0 ≤ a ∧ ∀ omega : ℝ, a < omega -> innerAt omega}
    let innerThreshold := sInf innerCandidates
    let criticalLine :=
      ∀ point : ℂ, xiReading point = 0 -> point.re = (1 : ℝ) / 2
    toroidalThreshold = innerThreshold ∧
      (criticalLine ↔ toroidalThreshold = 0) ∧
      (criticalLine ↔ innerThreshold = 0) := by
  let deviations : Set ℝ := {a | ∃ point : ℂ,
    (1 : ℝ) / 2 ≤ point.re ∧
    (∀ index, period index point = 0) ∧
    a = point.re - (1 : ℝ) / 2}
  let innerCandidates : Set ℝ :=
    {a | 0 ≤ a ∧ ∀ omega : ℝ, a < omega -> innerAt omega}
  let criticalLine :=
    ∀ point : ℂ, xiReading point = 0 -> point.re = (1 : ℝ) / 2
  change sSup deviations = sInf innerCandidates ∧
    (criticalLine ↔ sSup deviations = 0) ∧
    (criticalLine ↔ sInf innerCandidates = 0)
  change deviations.Nonempty at deviationNonempty
  change BddAbove deviations at deviationBounded
  have commonZeroIff (point : ℂ) :
      (∀ index, period index point = 0) ↔ xiReading point = 0 := by
    have locusEquality := toroidal_common_zero_locus
      (Omega := (Set.univ : Set ℂ)) period twist factorization
      (fun spectralPoint _ => pointwiseNonvanishing spectralPoint)
    have pointMembership := Set.ext_iff.mp locusEquality
      (⟨point, Set.mem_univ point⟩ : Set.univ)
    simpa only [Set.mem_setOf_eq] using pointMembership
  have candidatesEqUpperBounds : innerCandidates = upperBounds deviations := by
    ext a
    change (0 ≤ a ∧ ∀ omega : ℝ, a < omega -> innerAt omega) ↔
      ∀ d ∈ deviations, d ≤ a
    constructor
    · rintro ⟨ha, hInner⟩ d hd
      have hZeroBound := (suzukiEquivalence a ha).mp hInner
      rcases hd with ⟨point, hRight, hPeriods, rfl⟩
      have hXi := (commonZeroIff point).mp hPeriods
      have := hZeroBound point hXi
      linarith
    · intro hUpper
      have ha : 0 ≤ a := by
        obtain ⟨d, hd⟩ := deviationNonempty
        have hda := hUpper d hd
        rcases hd with ⟨point, hRight, _, rfl⟩
        linarith
      refine ⟨ha, (suzukiEquivalence a ha).mpr ?_⟩
      intro point hXi
      by_cases hRight : (1 : ℝ) / 2 ≤ point.re
      · have hPeriods := (commonZeroIff point).mpr hXi
        have hDeviation : point.re - (1 : ℝ) / 2 ∈ deviations :=
          ⟨point, hRight, hPeriods, rfl⟩
        have := hUpper _ hDeviation
        linarith
      · linarith
  have thresholdIdentity : sSup deviations = sInf innerCandidates := by
    rw [candidatesEqUpperBounds,
      csInf_upperBounds_eq_csSup deviationBounded deviationNonempty]
  have criticalLineIffToroidal : criticalLine ↔ sSup deviations = 0 := by
    constructor
    · intro hCritical
      apply le_antisymm
      · apply csSup_le deviationNonempty
        intro d hd
        rcases hd with ⟨point, _, hPeriods, rfl⟩
        have hXi := (commonZeroIff point).mp hPeriods
        have hFixed := hCritical point hXi
        linarith
      · obtain ⟨d, hd⟩ := deviationNonempty
        have hdSup := le_csSup deviationBounded hd
        rcases hd with ⟨point, hRight, _, rfl⟩
        linarith
    · intro hThreshold point hXi
      have rightHalfFixed (spectralPoint : ℂ)
          (hSpectralXi : xiReading spectralPoint = 0)
          (hRight : (1 : ℝ) / 2 ≤ spectralPoint.re) :
          spectralPoint.re = (1 : ℝ) / 2 := by
        have hPeriods := (commonZeroIff spectralPoint).mpr hSpectralXi
        have hDeviation : spectralPoint.re - (1 : ℝ) / 2 ∈ deviations :=
          ⟨spectralPoint, hRight, hPeriods, rfl⟩
        have hLeSup := le_csSup deviationBounded hDeviation
        rw [hThreshold] at hLeSup
        linarith
      by_cases hRight : (1 : ℝ) / 2 ≤ point.re
      · exact rightHalfFixed point hXi hRight
      · have hReflectedXi : xiReading (1 - point) = 0 := by
          rw [xi_reading_reflection, hXi]
        have hReflectedRight : (1 : ℝ) / 2 ≤ (1 - point).re := by
          simp only [Complex.sub_re, Complex.one_re]
          linarith
        have hReflectedFixed :=
          rightHalfFixed (1 - point) hReflectedXi hReflectedRight
        simp only [Complex.sub_re, Complex.one_re] at hReflectedFixed
        linarith
  refine ⟨thresholdIdentity, criticalLineIffToroidal, ?_⟩
  constructor
  · intro hCritical
    calc
      sInf innerCandidates = sSup deviations := thresholdIdentity.symm
      _ = 0 := criticalLineIffToroidal.mp hCritical
  · intro hInnerZero
    apply criticalLineIffToroidal.mpr
    calc
      sSup deviations = sInf innerCandidates := thresholdIdentity
      _ = 0 := hInnerZero

#print axioms toroidal_inner_threshold_identity

end D5.S3.Analytic.Adelic.ToroidalInnerThresholdIdentity
