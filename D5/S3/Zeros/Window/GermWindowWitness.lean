/- GID: D5/S3/Zeros/Window/GermWindowWitness
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An unconditional zero-count upper bound on a window crossing Re s = 1. -/
import Mathlib
import D5.S3.Zeros.Window.GermWindowCount

/- Provenance: Native proof over pinned mathlib. -/

/-!
SEARCH RECEIPT (2026-08-15, pinned repository and pinned mathlib):

* Searched the full `D5` tree for `Rectangle.*closedBall`,
  `closedBall.*Rectangle`, and `Rectangle z w ⊆`. The reusable public interface is
  `germWindowZeroCount_le` at
  `D5/S3/Zeros/Window/GermWindowCount.lean:83-99`; its rectangle containment
  remains a caller-supplied premise. The generic count definition and Jensen
  interface were read at
  `D5/S3/Zeros/Window/AnalyticWindowCount.lean:63-65,92-106`.
* Read `germ_product_ne_zero_of_re_ge` at
  `D5/S3/Analytic/EulerGerm/GermProductNonvanishing.lean:223-229` and
  `germProduct_analyticOnNhd` at
  `D5/S3/Analytic/EulerGerm/GermProductAnalytic.lean:146-162`. The former
  covers `Re s ≥ 1`, so the former center-`2` square lay wholly in the proved
  nonvanishing half-plane and has been removed as the load-bearing witness.
* `D5/S3/Zeros/Window/GermWindowCount.lean:101-108` contains the same
  inequality as `one_div_goldenRatio_sq_lt_half`, but that theorem is declared
  `private` and cannot be referenced across modules. The proof below instead
  derives the inequality from the public pinned-mathlib results
  `Real.goldenRatio_sq` and `Real.one_lt_goldenRatio`, read at
  `Mathlib/NumberTheory/Real/GoldenRatio.lean:82-84,90-98`.
* Read `Complex.mem_reProdIm` and `Complex.Rectangle` at
  `Mathlib/Data/Complex/Basic.lean:107-116,827-828`, `Set.uIcc_of_le` at
  `Mathlib/Order/Interval/Set/UnorderedInterval.lean:75-76`, and
  `Complex.norm_le_abs_re_add_abs_im` at
  `Mathlib/Analysis/Complex/Norm.lean:181-182`. They give the closed-ball
  containment proved below.
* The chosen rectangle has real interval `[7/8, 9/8]` and imaginary interval
  `[-1/8, 1/8]`. Thus it contains points with real part below and above `1`.
  The theorem supplies only an upper bound for its zero count; it does not
  assert that a zero exists or that the count is positive.
-/

open Complex Metric Set

namespace D5.S3.Zeros.Window.GermWindowWitness

open D5.S3.Analytic.EulerGerm.GermProductBound
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Zeros.Window.AnalyticWindowCount
open D5.S3.Zeros.Window.GermWindowCount

/-- The square of half-width `1/8` about `1` lies in the closed ball of radius
`1/4` about `1`. Its real interval is `[7/8, 9/8]`, so it crosses `Re s = 1`. -/
theorem germRectangle_subset_closedBall_one :
    Rectangle
        ((1 : ℂ) - 1 / 8 - (1 / 8) * Complex.I)
        ((1 : ℂ) + 1 / 8 + (1 / 8) * Complex.I) ⊆
      Metric.closedBall (1 : ℂ) |(1 / 4 : ℝ)| := by
  intro s hs
  rw [Rectangle, mem_reProdIm] at hs
  have hre_bounds :
      (1 : ℝ) - 1 / 8 ≤ s.re ∧ s.re ≤ (1 : ℝ) + 1 / 8 := by
    change s.re ∈ Set.Icc ((1 : ℝ) - 1 / 8) (1 + 1 / 8)
    rw [← Set.uIcc_of_le (by norm_num : (1 : ℝ) - 1 / 8 ≤ 1 + 1 / 8)]
    convert hs.1 using 1
    all_goals norm_num
  have him_bounds :
      -(1 / 8 : ℝ) ≤ s.im ∧ s.im ≤ (1 / 8 : ℝ) := by
    change s.im ∈ Set.Icc (-(1 / 8 : ℝ)) (1 / 8)
    rw [← Set.uIcc_of_le (by norm_num : -(1 / 8 : ℝ) ≤ 1 / 8)]
    convert hs.2 using 1
    all_goals norm_num
  have hre : |s.re - 1| ≤ (1 / 8 : ℝ) := by
    rw [abs_le]
    constructor <;> linarith [hre_bounds.1, hre_bounds.2]
  have him : |s.im| ≤ (1 / 8 : ℝ) := (abs_le).2 him_bounds
  rw [mem_closedBall, dist_eq_norm]
  calc
    ‖s - (1 : ℂ)‖ ≤ |(s - (1 : ℂ)).re| + |(s - (1 : ℂ)).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |s.re - 1| + |s.im| := by norm_num
    _ ≤ (1 / 8 : ℝ) + 1 / 8 := add_le_add hre him
    _ ≤ |(1 / 4 : ℝ)| := by norm_num

/-- The public germ-product estimate on a square whose real interval crosses
`Re s = 1`, with all six side conditions discharged. This is an upper bound
only and does not assert the existence of a zero in the square. -/
theorem germWindowZeroCount_le_crossing_one :
    windowZeroCount (fun s : ℂ => ∏' p : Nat.Primes, germLocalFactor s p)
        (Rectangle
          ((1 : ℂ) - 1 / 8 - (1 / 8) * Complex.I)
          ((1 : ℂ) + 1 / 8 + (1 / 8) * Complex.I))
      ≤ Real.log (germProductBound (1 / 2) /
            ‖∏' p : Nat.Primes, germLocalFactor (1 : ℂ) p‖) /
          Real.log ((1 / 2 : ℝ) / (1 / 4 : ℝ)) := by
  apply germWindowZeroCount_le (1 : ℂ)
      ((1 : ℂ) - 1 / 8 - (1 / 8) * Complex.I)
      ((1 : ℂ) + 1 / 8 + (1 / 8) * Complex.I)
      (1 / 4) (1 / 2) (1 / 2)
  · norm_num
  · have hsq : 2 < Real.goldenRatio ^ 2 := by
      rw [Real.goldenRatio_sq]
      linarith [Real.one_lt_goldenRatio]
    have hsq_pos : 0 < Real.goldenRatio ^ 2 := lt_trans (by norm_num) hsq
    rw [div_lt_iff₀ hsq_pos]
    nlinarith
  · norm_num
  · exact germRectangle_subset_closedBall_one
  · norm_num
  · norm_num

#print axioms germRectangle_subset_closedBall_one
#print axioms germWindowZeroCount_le_crossing_one

end D5.S3.Zeros.Window.GermWindowWitness
