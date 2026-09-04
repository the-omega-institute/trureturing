/- GID: D5/S3/Midline/Cayley/CayleyCriticalLineZetaCriterion
   generality: I
   mirror-B: D5/B/S3/Midline/Cayley/CayleyCriticalLineZetaCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cayley radial neutrality characterizes the critical line and Riemann hypothesis. -/

import D5.S3.Midline.Cayley.LogarithmicRadialDefect
import Mathlib.Tactic

/-!
# Cayley critical-line zeta criterion

This module retains the canonical Cayley coefficient `(s - 1) / s` and its
logarithmic radial defect from the existing midline family. It first identifies
the unit-norm locus of that coefficient for every complex point. It then
specializes the locus to Mathlib's exact nontrivial-zero premises and proves
that simultaneous radial neutrality is equivalent to `RiemannHypothesis`.

Library-search audit trail (2026-09-04):

* Repository body-shape searches found `cayleyCoefficient` and
  `logarithmicRadialDefect` in this family. They are imported as the canonical
  primitives. The nearby `logarithmic_radial_defect_and_mirror` theorem uses an
  abstract `ZeroData` carrier, so it does not state the zeta-level equivalence.
* Pinned Mathlib supplies `RiemannHypothesis`, `riemannZeta_zero`, complex norm
  and norm-square identities, and the positive-log zero criterion used below.
  No existing theorem combines the pointwise Cayley locus with Mathlib's
  nontrivial-zero quantification.
* Reachable third-party searches for the Cayley quotient and logarithmic radial
  criterion produced no Lean declaration with this two-clause statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Midline.Cayley.CayleyCriticalLineZetaCriterion

open D5.S3.Midline.Cayley.CayleyUnitarityDefect
open D5.S3.Midline.Cayley.LogarithmicRadialDefect

private theorem cayley_coefficient_norm_eq_one_iff (s : Complex) :
    ‖cayleyCoefficient s‖ = 1 ↔ s.re = (1 : Real) / 2 := by
  constructor
  · intro hUnit
    by_cases hs : s = 0
    · subst s
      norm_num [cayleyCoefficient] at hUnit
    · have hNorm : ‖s - 1‖ = ‖s‖ := by
        apply (div_eq_one_iff_eq (norm_ne_zero_iff.mpr hs)).mp
        simpa only [cayleyCoefficient, norm_div] using hUnit
      have hNormSq : Complex.normSq (s - 1) = Complex.normSq s := by
        simpa only [Complex.normSq_eq_norm_sq] using
          congrArg (fun x : Real => x ^ 2) hNorm
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
        Complex.sub_im, Complex.one_im, sub_zero] at hNormSq
      nlinarith
  · intro hLine
    have hs : s ≠ 0 := by
      intro hs
      subst s
      norm_num at hLine
    rw [cayleyCoefficient, norm_div,
      div_eq_one_iff_eq (norm_ne_zero_iff.mpr hs)]
    rw [← sq_eq_sq₀ (norm_nonneg (s - 1)) (norm_nonneg s),
      ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero]
    nlinarith

/-- The canonical Cayley coordinate has unit norm exactly on the critical line,
and the Riemann hypothesis is equivalent to vanishing logarithmic radial defect
at every Mathlib-nontrivial zeta zero. -/
theorem cayley_critical_line_zeta_criterion :
    (∀ s : Complex,
      ‖cayleyCoefficient s‖ = 1 ↔ s.re = (1 : Real) / 2) ∧
    (RiemannHypothesis ↔
      ∀ rho : Complex,
        riemannZeta rho = 0 →
        (¬∃ n : Nat, rho = -2 * (n + 1)) →
        rho ≠ 1 →
        logarithmicRadialDefect rho = 0) := by
  refine ⟨cayley_coefficient_norm_eq_one_iff, ?_⟩
  constructor
  · intro hHypothesis rho hZero hNontrivial hOne
    have hLine : rho.re = (1 : Real) / 2 :=
      hHypothesis rho hZero hNontrivial hOne
    have hUnit := (cayley_coefficient_norm_eq_one_iff rho).2 hLine
    simp [logarithmicRadialDefect, hUnit]
  · intro hRadial rho hZero hNontrivial hOne
    have hRho : rho ≠ 0 := by
      intro hRho
      subst rho
      rw [riemannZeta_zero] at hZero
      norm_num at hZero
    have hRatio : cayleyCoefficient rho ≠ 0 := by
      unfold cayleyCoefficient
      exact div_ne_zero (sub_ne_zero.mpr hOne) hRho
    have hNormPositive : 0 < ‖cayleyCoefficient rho‖ :=
      norm_pos_iff.mpr hRatio
    have hUnit : ‖cayleyCoefficient rho‖ = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero hNormPositive
        (by simpa only [logarithmicRadialDefect] using
          hRadial rho hZero hNontrivial hOne)
    exact (cayley_coefficient_norm_eq_one_iff rho).1 hUnit

#print axioms cayley_critical_line_zeta_criterion

end D5.S3.Midline.Cayley.CayleyCriticalLineZetaCriterion
