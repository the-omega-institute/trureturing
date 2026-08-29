/- GID: D5/S3/Analytic/Adelic/FiniteToroidalSpectralTomography
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/FiniteToroidalSpectralTomography
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Compact windows admit finite toroidal zero and multiplicity witnesses. -/

import D5.S3.Analytic.Adelic.FiniteToroidalFrameReconstruction
import Mathlib.Analysis.Analytic.Order

/- Library-search audit trail (2026-08-29):
   * Repository searches for finite toroidal zero tomography and finite
     analytic-order minima found no whole-statement owner.
   * The frozen `finite_toroidal_frame_reconstruction` theorem is the exact
     compact finite-subcover constituent. It is imported and applied to the
     inline normalized product family; it does not state either conclusion
     below and therefore is not an exact bind target.
   * The preceding divisor-gcd theorem treats an infinite family under global
     pointwise nonvanishing. It neither extracts a compact-window finite family
     nor states the selected-family common-zero set.
   * Pinned Mathlib has no toroidal tomography theorem. Its exact constituents
     `analyticOrderAt_mul`, `AnalyticAt.analyticOrderAt_eq_zero`, and the
     complete-lattice infimum laws are applied directly.
   * Body-shape searches found no canonical finite zero-tomography definition.
     This module introduces no `def` or `abbrev`; normalized periods are
     constructed inline from the canonical `xiReading` and the twist family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.FiniteToroidalSpectralTomography

open D5.S3.Analytic.Adelic.FiniteToroidalFrameReconstruction
open D5.S3.Zeros.CompletedZeta

/--
Every compact spectral window covered by analytic twist-nonvanishing loci has
a finite selected family whose normalized periods have exactly the xi zeros on
the window. At every point of the window, the xi vanishing order is also the
infimum, hence the minimum, of the selected period orders.
-/
theorem finite_toroidal_spectral_tomography {Index : Type*} (window : Set ℂ)
    (twist : Index -> ℂ -> ℂ)
    (twistDifferentiable : ∀ index, Differentiable ℂ (twist index))
    (windowCompact : IsCompact window)
    (pointwiseNonvanishing :
      ∀ point ∈ window, ∃ index, twist index point ≠ 0) :
    ∃ selected : Finset Index,
      {point | point ∈ window ∧
          ∀ index, index ∈ selected ->
            xiReading point * twist index point = 0} =
        {point | point ∈ window ∧ xiReading point = 0} ∧
      ∀ rho ∈ window,
        analyticOrderAt xiReading rho =
          ⨅ index : {candidate // candidate ∈ selected},
            analyticOrderAt
              (fun point => xiReading point * twist index.1 point) rho := by
  obtain ⟨selected, finiteNonvanishing, _⟩ :=
    finite_toroidal_frame_reconstruction window
      (fun index point => xiReading point * twist index point) twist
      (fun index => (twistDifferentiable index).continuous)
      (fun index point => rfl) windowCompact pointwiseNonvanishing
  refine ⟨selected, ?_, ?_⟩
  · ext point
    change
      (point ∈ window ∧
          ∀ index, index ∈ selected ->
            xiReading point * twist index point = 0) ↔
        point ∈ window ∧ xiReading point = 0
    constructor
    · rintro ⟨pointInWindow, allPeriodsZero⟩
      obtain ⟨index, indexSelected, twistNonzero⟩ :=
        finiteNonvanishing point pointInWindow
      have periodZero := allPeriodsZero index indexSelected
      exact ⟨pointInWindow,
        (mul_eq_zero.mp periodZero).resolve_right twistNonzero⟩
    · rintro ⟨pointInWindow, xiZero⟩
      refine ⟨pointInWindow, ?_⟩
      intro index _
      simp [xiZero]
  · intro rho rhoInWindow
    have xiAnalytic : AnalyticAt ℂ xiReading rho :=
      xi_reading_differentiable.analyticAt rho
    have twistAnalytic : ∀ index, AnalyticAt ℂ (twist index) rho :=
      fun index => (twistDifferentiable index).analyticAt rho
    have productOrder : ∀ index : {candidate // candidate ∈ selected},
        analyticOrderAt
            (fun point => xiReading point * twist index.1 point) rho =
          analyticOrderAt xiReading rho +
            analyticOrderAt (twist index.1) rho := by
      intro index
      change analyticOrderAt (xiReading * twist index.1) rho = _
      exact analyticOrderAt_mul xiAnalytic (twistAnalytic index.1)
    apply le_antisymm
    · apply le_iInf
      intro index
      rw [productOrder index]
      exact le_add_right le_rfl
    · obtain ⟨index, indexSelected, twistNonzero⟩ :=
        finiteNonvanishing rho rhoInWindow
      let selectedIndex : {candidate // candidate ∈ selected} :=
        ⟨index, indexSelected⟩
      calc
        (⨅ candidate : {index // index ∈ selected},
            analyticOrderAt
              (fun point => xiReading point * twist candidate.1 point) rho) ≤
            analyticOrderAt
              (fun point => xiReading point * twist selectedIndex.1 point) rho :=
          iInf_le _ selectedIndex
        _ = analyticOrderAt xiReading rho +
              analyticOrderAt (twist selectedIndex.1) rho :=
          productOrder selectedIndex
        _ = analyticOrderAt xiReading rho + 0 := by
          rw [(twistAnalytic selectedIndex.1).analyticOrderAt_eq_zero.mpr
            twistNonzero]
        _ = analyticOrderAt xiReading rho := add_zero _

example :
    ∃ (window : Set ℂ) (twist : Unit -> ℂ -> ℂ),
      IsCompact window ∧
        (∀ index, Differentiable ℂ (twist index)) ∧
        ∀ point ∈ window, ∃ index, twist index point ≠ 0 := by
  refine ⟨{0}, fun _ _ => 1, isCompact_singleton, ?_, ?_⟩
  · intro index
    fun_prop
  · intro point pointInWindow
    exact ⟨(), one_ne_zero⟩

#print axioms finite_toroidal_spectral_tomography

end D5.S3.Analytic.Adelic.FiniteToroidalSpectralTomography
