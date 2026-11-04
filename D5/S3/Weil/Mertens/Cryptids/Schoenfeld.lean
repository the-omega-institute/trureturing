/- GID: D5/S3/Weil/Mertens/Cryptids/Schoenfeld
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/Cryptids/Schoenfeld
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original Cryptids Analytic analytic source for the RH Chebyshev bound. -/

/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in
  docs/reports/licenses/cryptids-LICENSE.txt.
Source: https://github.com/google-deepmind/cryptids/blob/e5f59ed70d1549a61ef8873a6fbae9268fdbd557/Cryptids/Semantics/Riemann/Analytic.lean
Routing adaptations: ordinary D5 modules, redirected imports, and declaration-boundary splitting.
The original declaration namespaces, statements, and mathematical proof text are retained.
Retirement: when this repository's lake-manifest.json Mathlib revision provides an equivalent
RH-only real-x Chebyshev psi estimate for x >= 5000, replace the target with that declaration
and delete the transplanted declarations no longer in its live dependency closure.
-/

import D5.S3.Weil.Mertens.Cryptids.DigammaBinet
import D5.S3.Weil.Mertens.Cryptids.ExplicitLarge
import D5.S3.Weil.Mertens.Cryptids.HorizontalBounds
import D5.S3.Weil.Mertens.Cryptids.VonMangoldtCount
import D5.S3.Weil.Mertens.Cryptids.WeightedStieltjes

/-! Original Analytic analytic supplier for the RH Chebyshev estimate. -/

namespace ConjectureMachines.Semantics.Riemann




/-- Explicit Schoenfeld-type inequality at $x$:
$$|\psi(x) - x| \le \frac{7}{8} \sqrt{x} (\log x)^2.$$ -/
def SchoenfeldPsiBound (x : ℝ) : Prop :=
  |Chebyshev.psi x - x| ≤ (7 / 8 : ℝ) * Real.sqrt x * (Real.log x) ^ 2

/-- **Explicit Formula $\psi(x)$ Bound for $x \ge 5000$ under `RiemannHypothesis`**:
Combining the smoothed Perron contour shift and multiplicity-weighted Stieltjes bound
(`WeightedStieltjes`), the quartic Euler–Maclaurin Jensen zero-counting bound (`VonMangoldtCount`),
the Binet/Euler–Maclaurin digamma vertical bound (`DigammaBinet`), the Borel–Carathéodory
horizontal contour bound (`HorizontalBounds`), and the large-`x` real inequality (`ExplicitLarge`)
proves `SchoenfeldPsiBound x` for all `x ≥ 5000`. -/
theorem abs_psi_sub_self_le_seven_eighths_of_five_thousand_le (hRH : RiemannHypothesis)
    {x : ℝ} (hx : 5000 ≤ x) :
    SchoenfeldPsiBound x := by
  unfold SchoenfeldPsiBound
  obtain ⟨⟨hx_sub, hh_pos, h6T⟩, h_rhs⟩ :=
    ExplicitLarge.explicit_rhs_le_seven_eighths_of_five_thousand_le hx
  obtain ⟨C_h, hCh, h_heights_hb⟩ :=
    HorizontalBounds.exists_zero_free_height_with_log_pow_five_bound hRH h6T
  have hN_bound : ∀ t ≥ 6,
      (WeightedStieltjes.weightedZeroCountingFunction t : ℝ) ≤
        (16 / 5 : ℝ) * t * Real.log t + (11 / 5 : ℝ) * t + (0 : ℝ) := by
    intro t ht
    rw [add_zero]
    exact VonMangoldtCount.weightedZeroCountingFunction_le_sixteen_fifths hRH ht
  have h_left_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (1 : ℝ) * Real.log (|t| + 2) + (85 : ℝ) := by
    intro t
    have h_eq : (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (-1 / 4 : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [h_eq, neg_div, norm_neg, ← logDeriv_apply, one_mul]
    exact DigammaBinet.norm_logDeriv_riemannZeta_leftVertical_le_eighty_five t
  have h_explicit :=
    WeightedStieltjes.abs_psi_sub_self_le_weighted_riemannVonMangoldt_six_neg_one_fourth
      hRH hx_sub hh_pos h6T (by norm_num) (by norm_num) (by norm_num) (by norm_num) hCh
      hN_bound h_left_zeta h_heights_hb
  exact h_explicit.trans h_rhs

end ConjectureMachines.Semantics.Riemann
