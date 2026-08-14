/- GID: D5/S3/Zeros/Window/AnalyticWindowCount
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Jensen's disk bound controls the divisor count in any enclosed rectangular window. -/
import Mathlib

/- Provenance: Native proof over pinned mathlib. -/

/-!
SEARCH RECEIPT (2026-08-14, pinned repository and pinned mathlib):

Definition search, before proof:

* Rectangle: `Rectangle` was found in `Mathlib/Data/Complex/Basic.lean` as the product of two
  `uIcc`s. It is used directly. Exact searches for a named rectangle-compactness theorem had no
  hit; its compactness is supplied at the point of use by
  `isCompact_uIcc.reProdIm isCompact_uIcc`. No rectangle definition or compactness wrapper is
  introduced here.
* Window: `Zeta23.ZeroConfig.window` was found in `D5/S3/Weil/ZetaCore/Defs.lean`; it is an
  ordinate window inside a fixed zero configuration, not an arbitrary analytic domain. This file
  therefore takes the existing type `Set ℂ` as its window parameter and introduces no `window`
  definition.
* Count: `Zeta23.ZeroConfig.N` in `D5/S3/Weil/ZetaCore/Defs.lean`, and `Zeta23.Ncount` plus
  `Zeta23.zeroMult` in `D5/S3/Weil/ZetaCore/Statement.lean`, were found. They are natural-valued
  counts for an abstract zero configuration or specifically for zeta. Searches for
  `windowZeroCount` and for a named generic finsum of a meromorphic divisor had no other hit. Thus
  the one new definition below is the generic integer-valued divisor count required by this node.
* Zero set: `Zeta23.IsNontrivialZero` and `Zeta23.zerosIn` were found in
  `D5/S3/Weil/ZetaCore/Statement.lean`, and disk-specific `SetOfZeros` in
  `D5/S3/Weil/ZetaPntBase/StrongPNTPrefix.lean`. No zero-set definition is introduced here.
* Divisor: `MeromorphicOn.divisor` was found in
  `Mathlib/Analysis/Meromorphic/Divisor.lean` and is used directly, together with
  `AnalyticOnNhd.divisor_apply`, `AnalyticOnNhd.divisor_nonneg`,
  `divisor_support_finite_of_subset`, and `Function.locallyFinsuppWithin.finiteSupport`.

Theorem search and division of responsibility:

* `AnalyticOnNhd.sum_divisor_le` was found in
  `Mathlib/Analysis/Complex/JensenFormula.lean` and is invoked directly; no Jensen formula or
  disk estimate is reproved.
* Exact searches for a theorem asserting finite divisor support specifically on `Rectangle`
  had no hit. The final support theorem is therefore the direct specialization of mathlib's
  `finiteSupport` to the compact product of `uIcc`s.
* `Zeta23.Analytic.finite_zeros_rectangle` was found in
  `D5/S3/Weil/ZetaAnalytic/RectangleLogDeriv.lean` with the required zero-set finiteness statement.
  The previous revision cited that theorem but still reproved its result. This revision provides
  no zero-set finiteness theorem or thin wrapper.
* `D5/S3/Weil/ZetaRvm/CountByIntegral.lean`, `Halving.lean`, `LocalCount.lean`, and
  `ZetaGrowth.lean` contain the zeta Riemann--von Mangoldt counting machinery, including `Ncount`,
  `zeroMult`, `zetaZeroConfig.window`, and `zeta_local_zero_count`. The weighted argument principle
  `Zeta23.Analytic.rectangleIntegral'_mul_logDeriv` is in
  `D5/S3/Weil/ZetaAnalytic/RectangleLogDeriv.lean`. This file does not rebuild the argument
  principle or Riemann--von Mangoldt counts; it only bridges mathlib's Jensen disk bound to an
  enclosed rectangular window.
-/

open Complex Metric Set

namespace D5.S3.Zeros.Window.AnalyticWindowCount

/-- The zero count in a window, with analytic multiplicities supplied by the divisor. -/
noncomputable def windowZeroCount (f : ℂ → ℂ) (K : Set ℂ) : ℤ :=
  ∑ᶠ u, MeromorphicOn.divisor f K u

/-- An analytic function has a nonnegative divisor count on every window. -/
theorem windowZeroCount_nonneg {f : ℂ → ℂ} {K : Set ℂ}
    (hf : AnalyticOnNhd ℂ f K) :
    0 ≤ windowZeroCount f K := by
  exact finsum_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf)

/-- Divisor counts are monotone under inclusion into a compact analytic domain. -/
theorem windowZeroCount_mono {f : ℂ → ℂ} {K₁ K₂ : Set ℂ}
    (hK₁K₂ : K₁ ⊆ K₂) (hK₂ : IsCompact K₂) (hf : AnalyticOnNhd ℂ f K₂) :
    windowZeroCount f K₁ ≤ windowZeroCount f K₂ := by
  unfold windowZeroCount
  refine finsum_le_finsum' ?_ ?_ fun u ↦ ?_
  · exact hf.meromorphicOn.divisor_support_finite_of_subset hK₂ hK₁K₂
  · exact (MeromorphicOn.divisor f K₂).finiteSupport hK₂
  · by_cases hu : u ∈ K₁
    · rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (hf.mono hK₁K₂) hu,
        MeromorphicOn.AnalyticOnNhd.divisor_apply hf (hK₁K₂ hu)]
    · rw [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf u

/--
Jensen's disk estimate, transported to any closed rectangular window contained in the smaller
disk. The analytic, center, boundary-bound, and radius hypotheses are exactly those of mathlib's
`AnalyticOnNhd.sum_divisor_le`; only the rectangle inclusion is new.
-/
theorem windowZeroCount_le_log_div_log_of_rectangle_subset_closedBall
    {f : ℂ → ℂ} {ctr z w : ℂ} {r R M : ℝ}
    (hRect : Rectangle z w ⊆ closedBall ctr |r|)
    (r_pos : 0 < |r|) (r_lt_R : |r| < |R|) (hM : 1 ≤ M)
    (hf : AnalyticOnNhd ℂ f (closedBall ctr |R|)) (hf_ctr : f ctr ≠ 0)
    (f_bound : ∀ z ∈ sphere ctr |R|, ‖f z‖ ≤ M) :
    windowZeroCount f (Rectangle z w) ≤
      Real.log (M / ‖f ctr‖) / Real.log (R / r) := by
  calc
    (windowZeroCount f (Rectangle z w) : ℝ)
        ≤ (windowZeroCount f (closedBall ctr |r|) : ℝ) := by
      exact_mod_cast windowZeroCount_mono hRect (isCompact_closedBall ctr |r|)
          (hf.mono (closedBall_subset_closedBall r_lt_R.le))
    _ ≤ Real.log (M / ‖f ctr‖) / Real.log (R / r) := by
      simpa [windowZeroCount] using hf.sum_divisor_le r_pos r_lt_R hM hf_ctr f_bound

/-- The divisor underlying the count has finite support on every closed rectangle. -/
theorem finite_divisor_support_rectangle (f : ℂ → ℂ) (z w : ℂ) :
    (MeromorphicOn.divisor f (Rectangle z w)).support.Finite := by
  exact (MeromorphicOn.divisor f (Rectangle z w)).finiteSupport
    (isCompact_uIcc.reProdIm isCompact_uIcc)

end D5.S3.Zeros.Window.AnalyticWindowCount
