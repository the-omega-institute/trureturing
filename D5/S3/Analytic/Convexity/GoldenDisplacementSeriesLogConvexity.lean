/- GID: D5/S3/Analytic/Convexity/GoldenDisplacementSeriesLogConvexity
   generality: I
   mirror-B: D5/B/S3/Analytic/Convexity/GoldenDisplacementSeriesLogConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden displacement sum is log-convex throughout its exact convergence region. -/

/- Library-search audit trail (2026-08-27):
* Pinned Mathlib contains `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg`, but searches for Holder,
  rpow, tsum, summable, interpolation, and log-convex combinations found no theorem already
  packaging the needed weighted interpolation of two summable nonnegative families.
* Repository search found three implementations: the private `power_sum_interpolate` in the
  merged and frozen `Zeta/ZetaRenyiMonotone`, the private `logPartition_convex_combo` in the
  merged and frozen `ZetaEntropyPlane/TemperatureAntitone`, and the private derivation formerly
  in this module. The two zeta modules both carry 2026-08-23 search receipts and predate this node.
* Because the frozen modules cannot be edited, they cannot consume the extraction. Nevertheless,
  three independent implementations establish demand, and this node now consumes the public
  `countable_weighted_holder_interpolation` theorem in `Analytic/SeriesInequalities`.
-/

import D5.S3.Analytic.Displacement.GoldenDisplacementRegionConvexity
import D5.S3.Analytic.SeriesInequalities.CountableWeightedHolderInterpolation

open GoldenDisplacementEulerProduct
open GoldenDisplacementRegionConvexity
open GoldenDesubstitutionLength
open GoldenSubstitutionOrbit
open D5.S3.Analytic.SeriesInequalities.CountableWeightedHolderInterpolation

namespace D5.S3.Analytic.Convexity.GoldenDisplacementSeriesLogConvexity

noncomputable section

private abbrev displacementSum (s w : ℝ) : ℝ :=
  ∑' n : ℕ, dTerm s w n

private lemma dTerm_convex_combo (s1 w1 s2 w2 a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    dTerm (a * s1 + b * s2) (a * w1 + b * w2) n =
      dTerm s1 w1 n ^ a * dTerm s2 w2 n ^ b := by
  by_cases hn : n = 0
  · subst n
    rw [dTerm_zero, dTerm_zero, dTerm_zero, Real.zero_rpow ha.ne',
      Real.zero_rpow hb.ne', zero_mul]
  · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnSPos : (0 : ℝ) < nS n := by
      exact_mod_cast Nat.pos_of_ne_zero (nS_ne_zero n)
    unfold dTerm
    rw [if_neg hn, if_neg hn, if_neg hn]
    symm
    calc
      ((nS n : ℝ) ^ (-s1) * (n : ℝ) ^ (-w1)) ^ a *
          ((nS n : ℝ) ^ (-s2) * (n : ℝ) ^ (-w2)) ^ b =
          ((nS n : ℝ) ^ (-s1 * a) * (nS n : ℝ) ^ (-s2 * b)) *
            ((n : ℝ) ^ (-w1 * a) * (n : ℝ) ^ (-w2 * b)) := by
        rw [Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_mul hnSPos.le, ← Real.rpow_mul hnPos.le,
          ← Real.rpow_mul hnSPos.le, ← Real.rpow_mul hnPos.le]
        ring
      _ = (nS n : ℝ) ^ (-s1 * a + -s2 * b) *
          (n : ℝ) ^ (-w1 * a + -w2 * b) := by
        rw [← Real.rpow_add hnSPos, ← Real.rpow_add hnPos]
      _ = (nS n : ℝ) ^ (-(a * s1 + b * s2)) *
          (n : ℝ) ^ (-(a * w1 + b * w2)) := by
        ring_nf

private lemma displacementSum_log_convex_combo (s1 w1 s2 w2 a b : ℝ)
    (hs1 : Summable (dTerm s1 w1)) (hs2 : Summable (dTerm s2 w2))
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    displacementSum (a * s1 + b * s2) (a * w1 + b * w2) ≤
      displacementSum s1 w1 ^ a * displacementSum s2 w2 ^ b := by
  have hholder := countable_weighted_holder_interpolation
    (f := dTerm s1 w1) (g := dTerm s2 w2) (a := a) (b := b)
    (dTerm_nonneg s1 w1) (dTerm_nonneg s2 w2) hs1 hs2 ha hb hab
  calc
    displacementSum (a * s1 + b * s2) (a * w1 + b * w2) =
        ∑' n : ℕ, dTerm s1 w1 n ^ a * dTerm s2 w2 n ^ b :=
      tsum_congr fun n => dTerm_convex_combo s1 w1 s2 w2 a b ha hb n
    _ ≤ displacementSum s1 w1 ^ a * displacementSum s2 w2 ^ b := hholder

private lemma displacementSum_pos (s w : ℝ) (hs : Summable (dTerm s w)) :
    0 < displacementSum s w := by
  have hone : (1 : ℝ) ≤ displacementSum s w := by
    rw [← dTerm_one s w]
    exact hs.le_tsum 1 fun n _ => dTerm_nonneg s w n
  exact zero_lt_one.trans_le hone

private lemma displacementLog_convex_combo (s1 w1 s2 w2 a b : ℝ)
    (hs1 : Summable (dTerm s1 w1)) (hs2 : Summable (dTerm s2 w2))
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    Real.log (displacementSum (a * s1 + b * s2) (a * w1 + b * w2)) ≤
      a * Real.log (displacementSum s1 w1) +
        b * Real.log (displacementSum s2 w2) := by
  have hmixPair := golden_displacement_convergence_region_convex
    (x := (s1, w1)) hs1 (y := (s2, w2)) hs2 ha.le hb.le hab
  have hmix : Summable (dTerm (a * s1 + b * s2) (a * w1 + b * w2)) := by
    change Summable (dTerm (a * s1 + b * s2) (a * w1 + b * w2)) at hmixPair
    exact hmixPair
  have hbound := displacementSum_log_convex_combo s1 w1 s2 w2 a b
    hs1 hs2 ha hb hab
  have hpos1 := displacementSum_pos s1 w1 hs1
  have hpos2 := displacementSum_pos s2 w2 hs2
  have hposMix := displacementSum_pos _ _ hmix
  calc
    Real.log (displacementSum (a * s1 + b * s2) (a * w1 + b * w2)) ≤
        Real.log (displacementSum s1 w1 ^ a * displacementSum s2 w2 ^ b) :=
      Real.log_le_log hposMix hbound
    _ = a * Real.log (displacementSum s1 w1) +
        b * Real.log (displacementSum s2 w2) := by
      rw [Real.log_mul (Real.rpow_pos_of_pos hpos1 a).ne'
        (Real.rpow_pos_of_pos hpos2 b).ne', Real.log_rpow hpos1,
        Real.log_rpow hpos2]

/-- The logarithm of the golden displacement sum is convex on its exact convergence region. -/
theorem golden_displacement_series_log_convex :
    ConvexOn ℝ {p : ℝ × ℝ | Summable (dTerm p.1 p.2)}
      (fun p => Real.log (∑' n : ℕ, dTerm p.1 p.2 n)) := by
  rw [convexOn_iff_forall_pos]
  refine ⟨golden_displacement_convergence_region_convex, ?_⟩
  rintro ⟨s1, w1⟩ hs1 ⟨s2, w2⟩ hs2 a b ha hb hab
  change Real.log (displacementSum (a * s1 + b * s2) (a * w1 + b * w2)) ≤
    a * Real.log (displacementSum s1 w1) + b * Real.log (displacementSum s2 w2)
  exact
    displacementLog_convex_combo s1 w1 s2 w2 a b hs1 hs2 ha hb hab

end

end D5.S3.Analytic.Convexity.GoldenDisplacementSeriesLogConvexity
