/- GID: D5/S3/Weil/ZetaGamma/GoldenArchimedeanGap
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/GoldenArchimedeanGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound every nonzero golden observer mode by one positive Archimedean gap. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenVerticalSampling
import D5.S3.Weil.ZetaGamma.ArchimedeanObserverProductPositive

/-!
# Golden Archimedean gap

The logarithmic Archimedean dispersion is monotone in its squared-frequency parameter.
Every nonzero integral observer frequency is therefore bounded below by the fundamental
golden frequency, whose dispersion is strictly positive.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaGamma.GoldenArchimedeanGap

open D5.S3.Observer.GoldenPrimeCircle.GoldenVerticalSampling
open D5.S3.Weil.ZetaGamma.MasslessTangentConeLimit
open D5.S3.Weil.ZetaGamma.ArchimedeanObserverProductPositive

/-- The uniform gap is the Archimedean logarithmic tower at the fundamental golden
observer frequency. -/
noncomputable def goldenArchimedeanGap (sigma : ℝ) : ℝ :=
  archimedean_dispersion sigma (goldenAngularFrequency ^ 2)

/-- Increasing the nonnegative squared-frequency parameter increases the Archimedean
logarithmic tower. -/
theorem archimedean_dispersion_mono {sigma lambda mu : ℝ}
    (hsigma : 0 < sigma) (hlambda : 0 ≤ lambda) (hlambdaMu : lambda ≤ mu) :
    archimedean_dispersion sigma lambda ≤ archimedean_dispersion sigma mu := by
  have hmu : 0 ≤ mu := hlambda.trans hlambdaMu
  have hmajorant : Summable (fun m : ℕ => mu / (sigma + 2 * m) ^ 2) := by
    rw [← summable_nat_add_iff 1]
    have hp : Summable (fun n : ℕ => mu * (1 / ((n : ℝ) + 1) ^ 2)) := by
      have hp0 : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
        Real.summable_nat_pow_inv.mpr (by norm_num)
      have hp1 : Summable (fun n : ℕ => ((((n + 1 : ℕ) : ℝ) ^ 2)⁻¹)) :=
        (summable_nat_add_iff 1).mpr hp0
      refine (hp1.mul_left mu).congr ?_
      intro n
      push_cast
      simp only [one_div]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hp
    have hden : (n : ℝ) + 1 ≤ sigma + 2 * ((n + 1 : ℕ) : ℝ) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      push_cast
      nlinarith
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ hmu
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by positivity) hden 2)
  have hsum :
      Summable (fun m : ℕ => Real.log (1 + mu / (sigma + 2 * m) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun m => Real.log_nonneg ?_) (fun m => ?_) hmajorant
    · have hterm : 0 ≤ mu / (sigma + 2 * m) ^ 2 := by positivity
      linarith
    · have hpositive : 0 < 1 + mu / (sigma + 2 * m) ^ 2 := by positivity
      simpa using Real.log_le_sub_one_of_pos hpositive
  have hterm (m : ℕ) :
      Real.log (1 + lambda / (sigma + 2 * m) ^ 2) ≤
        Real.log (1 + mu / (sigma + 2 * m) ^ 2) := by
    apply Real.strictMonoOn_log.monotoneOn
    · rw [Set.mem_Ioi]
      positivity
    · rw [Set.mem_Ioi]
      positivity
    · gcongr
  have hlowerSum :
      Summable (fun m : ℕ => Real.log (1 + lambda / (sigma + 2 * m) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun m => Real.log_nonneg ?_) hterm hsum
    have htermNonnegative : 0 ≤ lambda / (sigma + 2 * m) ^ 2 := by positivity
    linarith
  unfold archimedean_dispersion
  exact hlowerSum.tsum_le_tsum hterm hsum

/-- On the source domain `sigma > 1`, every nonzero integral observer mode has
Archimedean cost at least the strictly positive fundamental golden gap. -/
theorem golden_archimedean_gap (sigma : ℝ) (hsigma : 1 < sigma)
    (n : ℤ) (hn : n ≠ 0) :
    goldenArchimedeanGap sigma ≤
        archimedean_dispersion sigma (((n : ℝ) * goldenAngularFrequency) ^ 2) ∧
      0 < goldenArchimedeanGap sigma := by
  have hsigmaPos : 0 < sigma := lt_trans zero_lt_one hsigma
  have hnSq : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases lt_or_gt_of_ne hn with hnNeg | hnPos
    · have hnLeInt : n ≤ -1 := by omega
      have hnLe : (n : ℝ) ≤ -1 := by exact_mod_cast hnLeInt
      nlinarith [sq_nonneg ((n : ℝ) + 1)]
    · have hnLeInt : 1 ≤ n := by omega
      have hnLe : (1 : ℝ) ≤ n := by exact_mod_cast hnLeInt
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  have hfrequencySq : goldenAngularFrequency ^ 2 ≤
      ((n : ℝ) * goldenAngularFrequency) ^ 2 := by
    calc
      goldenAngularFrequency ^ 2 = 1 * goldenAngularFrequency ^ 2 := by ring
      _ ≤ (n : ℝ) ^ 2 * goldenAngularFrequency ^ 2 :=
        mul_le_mul_of_nonneg_right hnSq (sq_nonneg goldenAngularFrequency)
      _ = ((n : ℝ) * goldenAngularFrequency) ^ 2 := by ring
  constructor
  · exact archimedean_dispersion_mono hsigmaPos
      (sq_nonneg goldenAngularFrequency) hfrequencySq
  · simpa [goldenArchimedeanGap] using
      (archimedean_observer_product_positive sigma goldenAngularFrequency hsigmaPos
        (ne_of_gt golden_angular_frequency_pos))

#print axioms archimedean_dispersion_mono
#print axioms golden_archimedean_gap

end D5.S3.Weil.ZetaGamma.GoldenArchimedeanGap
