/- GID: D5/S3/Analytic/ZetaObservation/LiouvilleParityHolomorphyCriterion
   generality: G
   mirror-B: D5/B/S3/Analytic/ZetaObservation/LiouvilleParityHolomorphyCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Holomorphy of the Liouville parity quotient characterizes the zeta zero line. -/

import D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
import D5.S3.Weil.ZetaSeam.StatementSeam
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic

/-!
# Liouville Parity Holomorphy Criterion

The quotient of the doubled zeta value by the zeta value has a local analytic
extension at every point of the open half-plane to the right of one half
exactly when the Riemann hypothesis holds. The punctured-neighborhood
formulation gives a literal meaning to the quotient at its apparent
singularities, including the pole of zeta at one.

Library-search audit trail (2026-09-04):

* Exact D5 searches for the first-power quotient criterion missed. The nearby
  `parity_polarization_holomorphy_criterion` concerns a squared denominator
  and has an additional reciprocal-order clause, so it is not an exact hit.
  The proof reuses `golden_right_half_strip_implies_rh`,
  `riemannZeta_analyticOnNhd_compl_one`, and
  `analyticOrderAt_riemannZeta_ne_top`.
* Pinned Mathlib defines `RiemannHypothesis` and supplies zeta factorization,
  analytic calculus, right-half-plane nonvanishing, and meromorphic-order
  calculus, but has no theorem with the complete equivalence.
* A GitHub Lean code search for the quotient together with
  `RiemannHypothesis` and for zeta analyticity together with that proposition
  returned no third-party exact hit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Set

namespace D5.S3.Analytic.ZetaObservation.LiouvilleParityHolomorphyCriterion

open D5.S3.Weil.ZetaBridge.RightHalfStripRiemannReduction
open Zeta23

/-- The Liouville parity quotient is holomorphic throughout the open
right half-plane exactly when all nontrivial zeta zeros lie on the critical
line. -/
theorem liouville_parity_holomorphy_criterion :
    let observationHalfPlane : Set ℂ := {s | (1 : ℝ) / 2 < s.re}
    let liouvilleParity : ℂ → ℂ := fun s =>
      riemannZeta (2 * s) / riemannZeta s
    let hasHolomorphicParity : Prop :=
      ∀ s ∈ observationHalfPlane,
        ∃ germ : ℂ → ℂ,
          AnalyticAt ℂ germ s ∧
          liouvilleParity =ᶠ[nhdsWithin s {s}ᶜ] germ
    RiemannHypothesis ↔ hasHolomorphicParity := by
  dsimp only
  constructor
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
    let extension : ℂ → ℂ := fun s =>
      riemannZeta (2 * s) * (s - 1) / riemannZeta₁ s
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
    refine ⟨extension,
      (hNumerator.mul (by fun_prop)).div hZetaOne (zetaOneNonzero s hs), ?_⟩
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
    dsimp only [extension]
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
            (fun z => riemannZeta (2 * z) / riemannZeta z) rho =
          ((-(multiplicity : ℤ) : ℤ) : WithTop ℤ) := by
      change meromorphicOrderAt
          ((fun z => riemannZeta (2 * z)) / riemannZeta) rho = _
      rw [meromorphicOrderAt_div hNumerator.meromorphicAt
        hZetaAnalytic.meromorphicAt]
      rw [hNumerator.meromorphicOrderAt_eq,
        hNumerator.analyticOrderAt_eq_zero.mpr hZetaTwoNonzero]
      rw [hZetaAnalytic.meromorphicOrderAt_eq, ← hMultiplicity]
      norm_num
    have hSameOrder := meromorphicOrderAt_congr hExtension
    have hNonnegative := hGermAnalytic.meromorphicOrderAt_nonneg
    rw [← hSameOrder, hQuotientOrder] at hNonnegative
    have hIntegerNonnegative : (0 : ℤ) ≤ -(multiplicity : ℤ) := by
      exact_mod_cast hNonnegative
    omega

#print axioms liouville_parity_holomorphy_criterion

end D5.S3.Analytic.ZetaObservation.LiouvilleParityHolomorphyCriterion
