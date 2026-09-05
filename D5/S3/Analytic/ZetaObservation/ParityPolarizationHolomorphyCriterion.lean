/- GID: D5/S3/Analytic/ZetaObservation/ParityPolarizationHolomorphyCriterion
   generality: G
   mirror-B: D5/B/S3/Analytic/ZetaObservation/ParityPolarizationHolomorphyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Holomorphy of the parity quotient characterizes the zeta zero line. -/

import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Weil.ZetaSeam.StatementSeam
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic

/-!
# Parity Polarization Holomorphy Criterion

The quotient of the doubled zeta value by the squared zeta value has a local
analytic extension at every point of the open right half-plane exactly when
the Riemann hypothesis holds. The punctured-neighborhood formulation gives a
literal meaning to the quotient at its apparent singularities, including the
pole of zeta at one.

The same theorem records the exact pole order of the reciprocal zeta
observer. The source restricts this consequence to zeros off the critical
line; the proof establishes it for every zeta zero, so no unused location
premise is introduced.

Library-search audit trail (2026-09-04):

* Exact D5 searches for the parity quotient and reciprocal-zeta pole order
  found no theorem covering both clauses. The proof reuses
  `golden_right_half_strip_implies_rh`,
  `riemannZeta_analyticOnNhd_compl_one`,
  `analyticOrderAt_riemannZeta_ne_top`, and `zeroMult`.
* Pinned Mathlib defines `RiemannHypothesis` and supplies the zeta residue
  factorization, analytic calculus, nonvanishing to the right of one, and
  meromorphic-order calculus, but has no exact theorem with this statement.
* Installed-package searches found no additional exact hit. The `Zeta23`
  declarations used here are the repository's attributed Apache-2.0 seam
  port.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Set

namespace D5.S3.Analytic.ZetaObservation.ParityPolarizationHolomorphyCriterion

open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
open Zeta23

/-- The doubled parity quotient is holomorphic throughout the open right
half-plane exactly when all nontrivial zeta zeros lie on the critical line;
the reciprocal observer has pole order equal to each zero multiplicity. -/
theorem parity_polarization_holomorphy_criterion :
    let observationHalfPlane : Set ℂ := {s | (1 : ℝ) / 2 < s.re}
    let parityPolarization : ℂ → ℂ := fun s =>
      riemannZeta (2 * s) / riemannZeta s ^ 2
    let mobiusObserver : ℂ → ℂ := fun s => (riemannZeta s)⁻¹
    let hasHolomorphicPolarization : Prop :=
      ∀ s ∈ observationHalfPlane,
        ∃ germ : ℂ → ℂ,
          AnalyticAt ℂ germ s ∧
          parityPolarization =ᶠ[nhdsWithin s {s}ᶜ] germ
    (RiemannHypothesis ↔ hasHolomorphicPolarization) ∧
      ∀ rho : ℂ, ∀ multiplicity : ℕ,
        riemannZeta rho = 0 →
        zeroMult rho = multiplicity →
        meromorphicOrderAt mobiusObserver rho = -(multiplicity : ℤ) := by
  dsimp only
  constructor
  · constructor
    · intro hRiemann
      have halfPlaneOpen : IsOpen {s : ℂ | (1 : ℝ) / 2 < s.re} :=
        isOpen_lt continuous_const Complex.continuous_re
      have zetaOneNonzero :
          ∀ s : ℂ, (1 : ℝ) / 2 < s.re → riemannZeta₁ s ≠ 0 := by
        intro s hs
        by_cases hsOne : s = 1
        · subst s
          simpa only [riemannZeta₁_one] using one_ne_zero
        · intro hZero
          have hZeta : riemannZeta s = 0 := by
            rw [riemannZeta_eq_inv_sub_mul hsOne, hZero, mul_zero]
          have hNotTrivial : ¬∃ n : ℕ, s = -2 * (n + 1) := by
            rintro ⟨n, hn⟩
            rw [hn] at hs
            norm_num at hs
            have hnNonnegative : (0 : ℝ) ≤ n := Nat.cast_nonneg n
            linarith
          have hLine := hRiemann s hZeta hNotTrivial hsOne
          linarith
      let polarization : ℂ → ℂ := fun s =>
        riemannZeta (2 * s) * (s - 1) ^ 2 / riemannZeta₁ s ^ 2
      intro s hs
      change (1 : ℝ) / 2 < s.re at hs
      have hTwoSNotOne : 2 * s ≠ 1 := by
        intro hEqual
        have hReal := congrArg Complex.re hEqual
        norm_num at hReal
        linarith
      have hNumerator : AnalyticAt ℂ (fun z => riemannZeta (2 * z)) s := by
        simpa only [Function.comp_def] using
          (riemannZeta_analyticOnNhd_compl_one (2 * s) hTwoSNotOne).comp
            (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 2 * z) s)
      have hZetaOne : AnalyticAt ℂ riemannZeta₁ s :=
        differentiable_riemannZeta₁.analyticAt s
      refine ⟨polarization,
        (hNumerator.mul (by fun_prop)).div (hZetaOne.pow 2)
          (pow_ne_zero 2 (zetaOneNonzero s hs)), ?_⟩
      have eventuallyHalfPlane :
          ∀ᶠ z in nhdsWithin s {s}ᶜ, (1 : ℝ) / 2 < z.re :=
        eventually_nhdsWithin_of_eventually_nhds (halfPlaneOpen.mem_nhds hs)
      have eventuallyNotOne : ∀ᶠ z in nhdsWithin s {s}ᶜ, z ≠ 1 := by
        by_cases hsOne : s = 1
        · subst s
          exact self_mem_nhdsWithin
        · exact eventually_ne_nhdsWithin hsOne
      filter_upwards [eventuallyHalfPlane, eventuallyNotOne] with z hzHalf hzOne
      have hZetaOneAtZ := zetaOneNonzero z hzHalf
      dsimp only [polarization]
      rw [riemannZeta_eq_inv_sub_mul hzOne]
      field_simp [sub_ne_zero.mpr hzOne, hZetaOneAtZ]
    · intro hHolomorphic
      apply golden_right_half_strip_implies_rh
      intro rho hZero hHalf hBelowOne
      have hRhoOne : rho ≠ 1 := by
        intro hEqual
        rw [hEqual] at hBelowOne
        norm_num at hBelowOne
      obtain ⟨germ, hGermAnalytic, hExtension⟩ :=
        hHolomorphic rho hHalf
      have hZetaAnalytic : AnalyticAt ℂ riemannZeta rho :=
        riemannZeta_analyticOnNhd_compl_one rho hRhoOne
      have hZetaOrderFinite : analyticOrderAt riemannZeta rho ≠ ⊤ :=
        analyticOrderAt_riemannZeta_ne_top hRhoOne
      have hZetaOrderNonzero : analyticOrderAt riemannZeta rho ≠ 0 :=
        hZetaAnalytic.analyticOrderAt_ne_zero.mpr hZero
      obtain ⟨multiplicity, hMultiplicity⟩ :=
        ENat.ne_top_iff_exists.mp hZetaOrderFinite
      have hMultiplicityPositive : 0 < multiplicity := by
        apply Nat.pos_of_ne_zero
        intro hMultiplicityZero
        apply hZetaOrderNonzero
        rw [← hMultiplicity, hMultiplicityZero]
        rfl
      have hTwoRho : 1 < (2 * rho).re := by
        norm_num [Complex.mul_re]
        linarith
      have hZetaTwoNonzero : riemannZeta (2 * rho) ≠ 0 :=
        riemannZeta_ne_zero_of_one_lt_re hTwoRho
      have hTwoRhoNotOne : 2 * rho ≠ 1 := by
        intro hEqual
        have hReal := congrArg Complex.re hEqual
        norm_num at hReal
        linarith
      have hNumerator : AnalyticAt ℂ (fun z => riemannZeta (2 * z)) rho := by
        simpa only [Function.comp_def] using
          (riemannZeta_analyticOnNhd_compl_one (2 * rho) hTwoRhoNotOne).comp
            (by fun_prop : AnalyticAt ℂ (fun z : ℂ => 2 * z) rho)
      have hQuotientOrder :
          meromorphicOrderAt
              (fun z => riemannZeta (2 * z) / riemannZeta z ^ 2) rho =
            ((-(2 * (multiplicity : ℤ)) : ℤ) : WithTop ℤ) := by
        change meromorphicOrderAt
            ((fun z => riemannZeta (2 * z)) / riemannZeta ^ 2) rho = _
        rw [meromorphicOrderAt_div hNumerator.meromorphicAt
          (hZetaAnalytic.pow 2).meromorphicAt]
        rw [hNumerator.meromorphicOrderAt_eq,
          hNumerator.analyticOrderAt_eq_zero.mpr hZetaTwoNonzero]
        rw [meromorphicOrderAt_pow hZetaAnalytic.meromorphicAt,
          hZetaAnalytic.meromorphicOrderAt_eq, ← hMultiplicity]
        norm_num
      have hSameOrder := meromorphicOrderAt_congr hExtension
      have hNonnegative := hGermAnalytic.meromorphicOrderAt_nonneg
      rw [← hSameOrder, hQuotientOrder] at hNonnegative
      have hIntegerNonnegative : (0 : ℤ) ≤ -(2 * (multiplicity : ℤ)) := by
        exact_mod_cast hNonnegative
      omega
  · intro rho multiplicity hZero hMultiplicity
    have hRhoOne : rho ≠ 1 := by
      intro hEqual
      subst rho
      exact riemannZeta_one_ne_zero hZero
    have hAnalytic : AnalyticAt ℂ riemannZeta rho :=
      riemannZeta_analyticOnNhd_compl_one rho hRhoOne
    have hFinite : analyticOrderAt riemannZeta rho ≠ ⊤ :=
      analyticOrderAt_riemannZeta_ne_top hRhoOne
    have hOrder : analyticOrderAt riemannZeta rho = (multiplicity : ℕ∞) := by
      unfold zeroMult at hMultiplicity
      obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hFinite
      rw [← hn] at hMultiplicity ⊢
      simpa using hMultiplicity
    change meromorphicOrderAt (riemannZeta⁻¹) rho = -(multiplicity : ℤ)
    rw [meromorphicOrderAt_inv, hAnalytic.meromorphicOrderAt_eq, hOrder]
    simp

#print axioms parity_polarization_holomorphy_criterion

end D5.S3.Analytic.ZetaObservation.ParityPolarizationHolomorphyCriterion
