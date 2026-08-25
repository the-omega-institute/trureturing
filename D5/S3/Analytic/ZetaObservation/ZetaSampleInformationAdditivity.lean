/- GID: D5/S3/Analytic/ZetaObservation/ZetaSampleInformationAdditivity
   generality: I
   mirror-B: D5/B/S3/Analytic/ZetaObservation/ZetaSampleInformationAdditivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fisher information adds across independent zeta samples. -/

import Mathlib.Probability.Moments.Variance
import D5.S3.Analytic.Zeta.ZetaEntropy

/-!
Library-search audit (2026-08-25): repository searches for Fisher information, independent-sample
information additivity, and an equality with a natural multiple found no existing declaration.
The existing zeta family supplies `zetaDist`, `zeta_real_apply`, and the logarithmic p-series
bound, but no second-moment or Fisher-information theorem.

Pinned Mathlib searches found no Fisher-information definition or theorem. The exact reusable
product result is `ProbabilityTheory.variance_sum_pi`: for a canonical finite product measure it
identifies the variance of a coordinate sum with the sum of the coordinate variances. The source's
immediately preceding theorem identifies one-sample zeta Fisher information with
`Var(log N)`, so the public statement below exposes that variance on the actual zeta law and its
canonical `m`-fold product. The only local analytic bridge proves that `log N` has a finite second
moment when `1 < s`.
-/

namespace D5.S3.Analytic.ZetaObservation.ZetaSampleInformationAdditivity

open scoped BigOperators
open MeasureTheory ProbabilityTheory
open D5.S3.Analytic.ZetaGibbs
open D5.S3.Analytic.Zeta.ZetaEntropy

noncomputable section

private lemma summable_log_sq_weight (s : Real) (hs : 1 < s) :
    Summable (fun n : Nat => Real.log n ^ 2 * (n : Real) ^ (-s)) := by
  let epsilon := (s - 1) / 4
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hexponent : 2 * epsilon - s < -1 := by
    dsimp [epsilon]
    linarith
  have hmajor :
      Summable (fun n : Nat => epsilon⁻¹ ^ 2 * (n : Real) ^ (2 * epsilon - s)) :=
    (Real.summable_nat_rpow.mpr hexponent).mul_left (epsilon⁻¹ ^ 2)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg n.cast_nonneg _))
    (fun n => ?_) hmajor
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [Real.zero_rpow (by linarith : -s ≠ 0),
      Real.zero_rpow (by linarith : 2 * epsilon - s ≠ 0)]
  · have hnR : 0 < (n : Real) := by exact_mod_cast hn
    have hlog : Real.log n <= (n : Real) ^ epsilon / epsilon :=
      Real.log_natCast_le_rpow_div n hepsilon
    have hsquare : Real.log n ^ 2 <= ((n : Real) ^ epsilon / epsilon) ^ 2 :=
      (sq_le_sq₀ (Real.log_natCast_nonneg n)
        (div_nonneg (Real.rpow_nonneg n.cast_nonneg _) hepsilon.le)).2 hlog
    calc
      Real.log n ^ 2 * (n : Real) ^ (-s) <=
          ((n : Real) ^ epsilon / epsilon) ^ 2 * (n : Real) ^ (-s) :=
        mul_le_mul_of_nonneg_right hsquare (Real.rpow_nonneg n.cast_nonneg _)
      _ = epsilon⁻¹ ^ 2 * (n : Real) ^ (2 * epsilon - s) := by
        rw [div_pow]
        calc
          ((n : Real) ^ epsilon) ^ 2 / epsilon ^ 2 * (n : Real) ^ (-s) =
              epsilon⁻¹ ^ 2 *
                (((n : Real) ^ epsilon) ^ 2 * (n : Real) ^ (-s)) := by ring_nf
          _ = epsilon⁻¹ ^ 2 * (n : Real) ^ (2 * epsilon - s) := by
            congr 1
            rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le,
              ← Real.rpow_add hnR]
            congr 1
            ring

private lemma zeta_log_memLp_two (s : Real) (hs : 1 < s) :
    MemLp (fun n : Nat => Real.log n) 2 (zetaDist s hs).toMeasure := by
  have hsummable :
      Summable (fun n : Nat =>
        pmfReal (zetaDist s hs) n * ‖Real.log n ^ 2‖) := by
    have hweighted :=
      (summable_log_sq_weight s hs).mul_right (partitionFunction s).toReal⁻¹
    apply hweighted.congr
    intro n
    rw [zeta_real_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log n))]
    ring
  apply (memLp_two_iff_integrable_sq AEStronglyMeasurable.of_discrete).2
  rw [← Measure.sum_smul_dirac (zetaDist s hs).toMeasure]
  apply integrable_sum_dirac
  · intro n
    exact measure_ne_top _ _
  · apply hsummable.congr
    intro n
    rw [PMF.toMeasure_apply_singleton (zetaDist s hs) n (MeasurableSet.singleton n)]
    rfl

/-- For `m` independent zeta samples, Fisher information is `m` times the one-sample
information. The source's variance characterization is displayed directly: the left side is the
variance of the sum of logarithmic coordinate observations under the canonical product zeta law,
and the right side is `m` times the one-coordinate variance. -/
theorem zeta_sample_information_additive (s : Real) (hs : 1 < s) (m : Nat) :
    variance
        (fun sample : Fin m -> Nat => ∑ i, Real.log (sample i))
        (Measure.pi (fun _ : Fin m => (zetaDist s hs).toMeasure)) =
      (m : Real) * variance (fun n : Nat => Real.log n) (zetaDist s hs).toMeasure := by
  calc
    variance
        (fun sample : Fin m -> Nat => ∑ i, Real.log (sample i))
        (Measure.pi (fun _ : Fin m => (zetaDist s hs).toMeasure)) =
      variance
        (∑ i : Fin m, fun sample : Fin m -> Nat => Real.log (sample i))
        (Measure.pi (fun _ : Fin m => (zetaDist s hs).toMeasure)) := by
          apply variance_congr
          exact Filter.Eventually.of_forall fun sample => by simp
    _ = (m : Real) * variance (fun n : Nat => Real.log n) (zetaDist s hs).toMeasure := by
      simpa using variance_sum_pi (fun _ : Fin m => zeta_log_memLp_two s hs)

#print axioms zeta_sample_information_additive

end

end D5.S3.Analytic.ZetaObservation.ZetaSampleInformationAdditivity
