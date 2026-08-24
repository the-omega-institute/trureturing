/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceNegativeBoundaryLinePositiveFailure
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bounds goldenSubstStart<=2v tightly; s<0 converges iff 1<2s+w; s>0 witness diverges. -/

import D5.S1.Deficit.Displacement.DisplacementSeriesDivergence
import D5.S1.Words.GoldenDensity
import D5.S3.Analytic.Displacement.GoldenDisplacementSurfaceExactRegion

/-! SEARCH RECEIPT

Repository searches:
* Found `D5.S1.Words.golden_window_true_discrepancy` in
  `D5/S1/Words/GoldenDensity.lean`; it directly controls the count used by
  `goldenSubstStart`, so no filtered-finset cardinality proof is repeated.
* Found `D5.S1.Words.goldenWindowTrueCount_eq_floor` in
  `D5/S1/Words/GoldenBalance.lean`, but the discrepancy theorem is closer to
  the required inequality.
* Found `GoldenDisplacementEulerProduct.self_le_goldenSubstStart` in
  `D5/S1/Deficit/Displacement/GoldenDisplacementEulerProduct.lean`; it is the
  complementary lower bound, not the upper bound required here.
* Found and reused
  `D5.S1.Deficit.Displacement.DisplacementSeriesDivergence.
  dTerm_not_summable_of_two_mul_add_le_one` for the sign-free forward
  implication from summability to `1 < 2 * s + w`.
* Found `GoldenDisplacementSurfaceExactRegion.dTerm_summable_iff`; it supplies
  the countable family used by the negative-side reverse implication.
* No repository declaration matching the upper bound, the negative-side
  reverse implication, or the positive-side counterexample was found.

Pinned mathlib searches:
* Found `Real.one_lt_goldenRatio` and `inv_lt_one_of_one_lt₀`; together they
  give `Real.goldenRatio⁻¹ < 1`.
* Found `mul_le_mul_of_nonneg_left`, `mul_le_mul_of_nonpos_left`, and
  `mul_lt_mul_of_pos_right`, used for the sign-sensitive scaling steps.
-/

open D5.S1.Words
open D5.S1.Deficit.Displacement.DisplacementSeriesDivergence
open GoldenDisplacementEulerProduct

namespace GoldenDisplacementSurfaceNegativeBoundaryLinePositiveFailure

noncomputable section

/-- Every golden substitution block starts no later than twice its input index. -/
theorem goldenSubstStart_le_two_mul (v : ℕ) :
    goldenSubstStart v ≤ 2 * v := by
  have hinv : Real.goldenRatio⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio
  have hdisc := golden_window_true_discrepancy 0 v
  rw [abs_lt] at hdisc
  have hscaled :
      (v : ℝ) * Real.goldenRatio⁻¹ ≤ (v : ℝ) := by
    simpa using mul_le_mul_of_nonneg_left hinv.le (by positivity : (0 : ℝ) ≤ v)
  have hcountReal :
      (goldenWindowTrueCount 0 v : ℝ) < (v : ℝ) + 1 := by
    linarith [hdisc.2, hscaled]
  have hcountNat : goldenWindowTrueCount 0 v < v + 1 := by
    exact_mod_cast hcountReal
  simp only [goldenSubstStart]
  omega

/-- The uniform factor two is attained by the first nonempty substitution prefix. -/
theorem goldenSubstStart_one_eq_two : goldenSubstStart 1 = 2 := by
  decide

/-- For negative `s`, convergence is equivalent to the `k = 0` line.
The forward implication reuses the sign-free frozen divergence theorem; the reverse uses the
substitution-start bound proved above. -/
theorem dTerm_summable_iff_of_neg {s w : ℝ} (hs : s < 0) :
    Summable (dTerm s w) ↔ 1 < 2 * s + w := by
  constructor
  · intro hsum
    by_contra hline
    exact dTerm_not_summable_of_two_mul_add_le_one (le_of_not_gt hline) hsum
  · rw [GoldenDisplacementSurfaceExactRegion.dTerm_summable_iff]
    intro hline k
    let v := k + 1
    have hvNat : 1 ≤ v := by
      dsimp [v]
      omega
    have hgNat : goldenSubstStart v ≤ 2 * v :=
      goldenSubstStart_le_two_mul v
    have hg :
        (goldenSubstStart v : ℝ) ≤ 2 * (v : ℝ) := by
      exact_mod_cast hgNat
    have hmul :
        s * (2 * (v : ℝ)) ≤ s * (goldenSubstStart v : ℝ) :=
      mul_le_mul_of_nonpos_left hg hs.le
    have hvPos : (0 : ℝ) < v := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hvNat)
    have hlineScaled := mul_lt_mul_of_pos_right hline hvPos
    have hvResult :
        1 < s * (goldenSubstStart v : ℝ) + w * (v : ℝ) := by
      calc
        1 ≤ (v : ℝ) := by exact_mod_cast hvNat
        _ < (2 * s + w) * (v : ℝ) := by simpa using hlineScaled
        _ = s * (2 * (v : ℝ)) + w * (v : ℝ) := by ring
        _ ≤ s * (goldenSubstStart v : ℝ) + w * (v : ℝ) :=
          add_le_add hmul (le_refl _)
    simpa only [v, Nat.cast_add, Nat.cast_one] using hvResult

/-- Above the same line with positive `s`, the displacement series can still diverge. -/
theorem exists_pos_above_two_mul_add_line_not_summable :
    ∃ s w : ℝ, 0 < s ∧ 1 < 2 * s + w ∧ ¬Summable (dTerm s w) := by
  refine ⟨3, -4, by norm_num, by norm_num, ?_⟩
  intro hsum
  have hfamily :=
    (GoldenDisplacementSurfaceExactRegion.dTerm_summable_iff 3 (-4)).mp hsum
  have hsecond := hfamily 1
  have hstartTwo : goldenSubstStart 2 = 3 := by
    decide
  norm_num [hstartTwo] at hsecond

end

end GoldenDisplacementSurfaceNegativeBoundaryLinePositiveFailure
