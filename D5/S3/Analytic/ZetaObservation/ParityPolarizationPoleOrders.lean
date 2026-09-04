/- GID: D5/S3/Analytic/ZetaObservation/ParityPolarizationPoleOrders
   generality: G
   mirror-B: D5/B/S3/Analytic/ZetaObservation/ParityPolarizationPoleOrders
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Parity holomorphy and all three observer pole orders share one criterion. -/

import D5.S3.Analytic.ZetaObservation.ParityPolarizationHolomorphyCriterion

/-!
# Parity polarization pole orders

The frozen parity-polarization criterion already identifies the Riemann
hypothesis with holomorphy of the doubled quotient and proves the reciprocal
zeta pole order. This module keeps that owner and adds the two source clauses
for the Liouville quotient and normalized parity polarization.

The pole-order clauses are stated for a zero in the observation half-plane.
This is the source's preceding definition of a right-side off-line zero, and
it ensures that the numerator at the doubled point is analytic and nonzero.

Library-search audit trail (2026-09-04):

* Whole-statement and body-shape D5 searches found the frozen
  `parity_polarization_holomorphy_criterion`, which is applied directly, but
  no owner for either remaining quotient order.
* Pinned Mathlib has no combined parity-observer theorem. It supplies
  `riemannZeta_ne_zero_of_one_lt_re`, analytic order at a zeta zero, and the
  meromorphic quotient and power laws applied below.
* Searches of every installed non-Mathlib package found no relevant
  declaration. The proof therefore uses only the frozen D5 owner and pinned
  Mathlib constituents.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Set

namespace D5.S3.Analytic.ZetaObservation.ParityPolarizationPoleOrders

open D5.S3.Analytic.ZetaObservation.ParityPolarizationHolomorphyCriterion
open Zeta23

/-- Holomorphy of the normalized parity polarization characterizes the zeta
zero line. At every zeta zero in the observation half-plane, the reciprocal
and Liouville observers have pole order equal to the zero multiplicity, while
the normalized polarization has twice that pole order. -/
theorem parity_polarization_holomorphy_and_pole_orders :
    let observationHalfPlane : Set ℂ := {s | (1 : ℝ) / 2 < s.re}
    let parityPolarization : ℂ → ℂ := fun s =>
      riemannZeta (2 * s) / riemannZeta s ^ 2
    let mobiusObserver : ℂ → ℂ := fun s => (riemannZeta s)⁻¹
    let liouvilleObserver : ℂ → ℂ := fun s =>
      riemannZeta (2 * s) / riemannZeta s
    let hasHolomorphicPolarization : Prop :=
      ∀ s ∈ observationHalfPlane,
        ∃ germ : ℂ → ℂ,
          AnalyticAt ℂ germ s ∧
          parityPolarization =ᶠ[nhdsWithin s {s}ᶜ] germ
    (RiemannHypothesis ↔ hasHolomorphicPolarization) ∧
      ∀ rho : ℂ, ∀ multiplicity : ℕ,
        rho ∈ observationHalfPlane →
        riemannZeta rho = 0 →
        zeroMult rho = multiplicity →
        meromorphicOrderAt mobiusObserver rho = -(multiplicity : ℤ) ∧
          meromorphicOrderAt liouvilleObserver rho = -(multiplicity : ℤ) ∧
          meromorphicOrderAt parityPolarization rho = -(2 * multiplicity : ℤ) := by
  dsimp only
  have baseCriterion := parity_polarization_holomorphy_criterion
  dsimp only at baseCriterion
  refine ⟨baseCriterion.1, ?_⟩
  intro rho multiplicity hHalfPlane hZero hMultiplicity
  change (1 : ℝ) / 2 < rho.re at hHalfPlane
  have hTwoRho : 1 < (2 * rho).re := by
    norm_num [Complex.mul_re]
    linarith
  have hNumeratorNonzero : riemannZeta (2 * rho) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hTwoRho
  have hRhoNotOne : rho ≠ 1 := by
    intro hEqual
    subst rho
    exact riemannZeta_one_ne_zero hZero
  have hTwoRhoNotOne : 2 * rho ≠ 1 := by
    intro hEqual
    have hReal := congrArg Complex.re hEqual
    have hTwoRhoReal : 1 < 2 * rho.re := by
      simpa [Complex.mul_re] using hTwoRho
    norm_num [Complex.mul_re] at hReal
    linarith
  have hNumeratorAnalytic :
      AnalyticAt ℂ (fun z => riemannZeta (2 * z)) rho := by
    simpa only [Function.comp_def] using
      (riemannZeta_analyticOnNhd_compl_one (2 * rho) hTwoRhoNotOne).comp
        (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 2 * z) rho)
  have hZetaAnalytic : AnalyticAt ℂ riemannZeta rho :=
    riemannZeta_analyticOnNhd_compl_one rho hRhoNotOne
  have hZetaOrderFinite : analyticOrderAt riemannZeta rho ≠ ⊤ :=
    analyticOrderAt_riemannZeta_ne_top hRhoNotOne
  have hZetaOrder : analyticOrderAt riemannZeta rho = (multiplicity : ℕ∞) := by
    unfold zeroMult at hMultiplicity
    obtain ⟨order, hOrder⟩ := ENat.ne_top_iff_exists.mp hZetaOrderFinite
    rw [← hOrder] at hMultiplicity ⊢
    simpa using hMultiplicity
  refine ⟨baseCriterion.2 rho multiplicity hZero hMultiplicity, ?_, ?_⟩
  · change meromorphicOrderAt
      ((fun z => riemannZeta (2 * z)) / riemannZeta) rho =
        -(multiplicity : ℤ)
    rw [meromorphicOrderAt_div hNumeratorAnalytic.meromorphicAt
      hZetaAnalytic.meromorphicAt]
    rw [hNumeratorAnalytic.meromorphicOrderAt_eq,
      hNumeratorAnalytic.analyticOrderAt_eq_zero.mpr hNumeratorNonzero]
    rw [hZetaAnalytic.meromorphicOrderAt_eq, hZetaOrder]
    norm_num
  · change meromorphicOrderAt
      ((fun z => riemannZeta (2 * z)) / riemannZeta ^ 2) rho =
        -(2 * multiplicity : ℤ)
    rw [meromorphicOrderAt_div hNumeratorAnalytic.meromorphicAt
      (hZetaAnalytic.pow 2).meromorphicAt]
    rw [hNumeratorAnalytic.meromorphicOrderAt_eq,
      hNumeratorAnalytic.analyticOrderAt_eq_zero.mpr hNumeratorNonzero]
    rw [meromorphicOrderAt_pow hZetaAnalytic.meromorphicAt,
      hZetaAnalytic.meromorphicOrderAt_eq, hZetaOrder]
    norm_num

#print axioms parity_polarization_holomorphy_and_pole_orders

end D5.S3.Analytic.ZetaObservation.ParityPolarizationPoleOrders
