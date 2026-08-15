/- GID: D5/S3/Zeros/Window/GermWindowCount
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Jensen's bound gives a witnessed zero-count estimate for the golden Euler germ. -/
import Mathlib
import D5.S3.Zeros.Window.AnalyticWindowCount
import D5.S3.Analytic.EulerGerm.GermProductAnalytic
import D5.S3.Analytic.EulerGerm.GermProductNonvanishing
import D5.S3.Analytic.EulerGerm.GermProductBound
import D5.S3.Analytic.EulerGerm.GoldenLocalFactor

/- Provenance: Native proof over pinned mathlib. -/

/-!
SEARCH RECEIPT (2026-08-15, pinned repository and pinned mathlib):

* Searched the full `D5` tree for `closedBall.*re`, `re.*closedBall`,
  `subset_re_ge`, `Rectangle.*closedBall`, and `windowZeroCount`. No public
  closed-ball-to-real-half-plane lemma and no germ zero-count application were
  found. The generic Jensen interface was read at
  `D5/S3/Zeros/Window/AnalyticWindowCount.lean:92-106` and is used directly.
* Read `germProduct_analyticOnNhd` at
  `D5/S3/Analytic/EulerGerm/GermProductAnalytic.lean:147-161`,
  `germ_product_ne_zero_of_re_ge` at
  `D5/S3/Analytic/EulerGerm/GermProductNonvanishing.lean:225-229`, and
  `one_le_germProductBound` plus `germProduct_norm_le` at
  `D5/S3/Analytic/EulerGerm/GermProductBound.lean:168-190`. These frozen
  results supply the analytic, nonvanishing, and uniform-bound inputs without
  reproving them. The local factor definition was read at
  `D5/S3/Analytic/EulerGerm/GoldenLocalFactor.lean:39-40`.
* Read `RCLike.abs_re_le_norm` at
  `Mathlib/Analysis/RCLike/Basic.lean:690-692` and
  `RCLike.re_le_norm` at lines 704-705. The former is used in the one new
  geometric lemma below. Read `Metric.sphere_subset_closedBall` at
  `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:480`, and use it to pass the
  half-plane estimate from the closed ball to its sphere.
* Read `Real.goldenRatio_sq` at
  `Mathlib/NumberTheory/Real/GoldenRatio.lean:83-84` and
  `Real.one_lt_goldenRatio` at lines 96-97. They prove the numeric
  specialization's golden-ratio condition, `1 / goldenRatio ^ 2 < 1 / 2`.
* Read `Complex.reProdIm` and `Complex.mem_reProdIm` at
  `Mathlib/Data/Complex/Basic.lean:109-116`, `Complex.Rectangle` at line 828,
  and `Complex.ext` at line 60. Read `Set.uIcc` and `Set.uIcc_self` at
  `Mathlib/Order/Interval/Set/UnorderedInterval.lean:59` and line 86, and
  `Metric.mem_closedBall_self` at
  `Mathlib/Topology/MetricSpace/Pseudo/Defs.lean:460-461`. These definitions
  and lemmas show that `Rectangle 2 2` is the singleton point `2`, hence is
  contained in the closed ball centered at `2`.
-/

open Complex Metric Set

namespace D5.S3.Zeros.Window.GermWindowCount

open D5.S3.Zeros.Window.AnalyticWindowCount
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.GermProductAnalytic
open D5.S3.Analytic.EulerGerm.GermProductNonvanishing
open D5.S3.Analytic.EulerGerm.GermProductBound

/-- A closed complex ball lies to the right of the vertical line obtained by
subtracting its radius from the real part of its center. -/
theorem closedBall_subset_re_ge (ctr : ℂ) (R σ : ℝ)
    (hσ : σ ≤ ctr.re - |R|) :
    closedBall ctr |R| ⊆ {s : ℂ | σ ≤ s.re} := by
  intro s hs
  have hnorm : ‖s - ctr‖ ≤ |R| := by
    simpa [dist_eq_norm] using (mem_closedBall.mp hs)
  have hre : ctr.re - s.re ≤ |R| := by
    calc
      ctr.re - s.re = -((s - ctr).re) := by simp
      _ ≤ |(s - ctr).re| := neg_le_abs _
      _ ≤ ‖s - ctr‖ := by
        simpa using (RCLike.abs_re_le_norm (K := ℂ) (s - ctr))
      _ ≤ |R| := hnorm
  change σ ≤ s.re
  linarith

/-- The frozen Jensen window estimate specialized to the golden Euler germ
prime product. -/
theorem germWindowZeroCount_le (ctr z w : ℂ) (r R σ : ℝ)
    (hctr : 1 ≤ ctr.re)
    (hσlo : 1 / Real.goldenRatio ^ 2 < σ)
    (hσhi : σ ≤ ctr.re - |R|)
    (hRect : Rectangle z w ⊆ Metric.closedBall ctr |r|)
    (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) :
    windowZeroCount (fun s : ℂ => ∏' p : Nat.Primes, germLocalFactor s p) (Rectangle z w)
      ≤ Real.log (germProductBound σ /
            ‖∏' p : Nat.Primes, germLocalFactor ctr p‖) / Real.log (R / r) := by
  apply windowZeroCount_le_log_div_log_of_rectangle_subset_closedBall
      hRect r_pos r_lt_R (one_le_germProductBound σ hσlo)
  · exact germProduct_analyticOnNhd.mono fun s hs =>
      lt_of_lt_of_le hσlo (closedBall_subset_re_ge ctr R σ hσhi hs)
  · exact germ_product_ne_zero_of_re_ge ctr hctr
  · intro s hs
    exact germProduct_norm_le σ hσlo s
      (closedBall_subset_re_ge ctr R σ hσhi (sphere_subset_closedBall hs))

private theorem one_div_goldenRatio_sq_lt_half :
    1 / Real.goldenRatio ^ 2 < (1 / 2 : ℝ) := by
  have hsq : 2 < Real.goldenRatio ^ 2 := by
    rw [Real.goldenRatio_sq]
    linarith [Real.one_lt_goldenRatio]
  have hsq_pos : 0 < Real.goldenRatio ^ 2 := lt_trans (by norm_num) hsq
  rw [div_lt_iff₀ hsq_pos]
  nlinarith

/-- Once rectangle containment is supplied, the five numerical side conditions
hold at center `2`, outer radius `1`, inner radius `1/2`, and boundary `1/2`. -/
theorem germWindowZeroCount_le_two (z w : ℂ)
    (hRect : Rectangle z w ⊆ Metric.closedBall (2 : ℂ) |(1 / 2 : ℝ)|) :
    windowZeroCount (fun s : ℂ => ∏' p : Nat.Primes, germLocalFactor s p) (Rectangle z w)
      ≤ Real.log (germProductBound (1 / 2) /
            ‖∏' p : Nat.Primes, germLocalFactor (2 : ℂ) p‖) /
          Real.log ((1 : ℝ) / (1 / 2 : ℝ)) := by
  apply germWindowZeroCount_le (2 : ℂ) z w (1 / 2) 1 (1 / 2)
  · norm_num
  · exact one_div_goldenRatio_sq_lt_half
  · norm_num
  · exact hRect
  · norm_num
  · norm_num

/-- All six side conditions are jointly witnessed by the point rectangle at
`2`; in particular, this zero-count estimate has no hypotheses. -/
theorem germWindowZeroCount_le_two_point :
    windowZeroCount (fun s : ℂ => ∏' p : Nat.Primes, germLocalFactor s p)
        (Rectangle (2 : ℂ) (2 : ℂ))
      ≤ Real.log (germProductBound (1 / 2) /
            ‖∏' p : Nat.Primes, germLocalFactor (2 : ℂ) p‖) /
          Real.log ((1 : ℝ) / (1 / 2 : ℝ)) := by
  apply germWindowZeroCount_le_two (2 : ℂ) (2 : ℂ)
  intro s hs
  rw [Rectangle, mem_reProdIm] at hs
  have hs_eq : s = (2 : ℂ) := by
    apply Complex.ext
    · simpa [Set.uIcc_self] using hs.1
    · simpa [Set.uIcc_self] using hs.2
  subst s
  exact mem_closedBall_self (abs_nonneg _)

#print axioms closedBall_subset_re_ge
#print axioms germWindowZeroCount_le
#print axioms germWindowZeroCount_le_two
#print axioms germWindowZeroCount_le_two_point

end D5.S3.Zeros.Window.GermWindowCount
