/- GID: D5/S3/Analytic/Convexity/PositivePairedPoissonCubature
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/PositivePairedPoissonCubature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Caratheodory, mathlib/module/Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional]
   utility: none
   digest: Positive paired Poisson cubature with at most L+1 phases for all first L signed cosine moments. -/

import D5.S3.Analytic.Convexity.MeasurableFiniteMoments
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Algebra.BigOperators.Pi

/-!
Exact finite positive cubature for geometrically weighted real cosine data.
The positive density and its probability normalization are constructed from the
coefficients; positive-index coefficients may have either sign. The moment
carrier is Fin L → ℝ, so probability mass uses no additional coordinate.

The actual-convex-hull foundation is imported from MeasurableFiniteMoments.
For its classical finite-cubature provenance, see Bayer and Teichmann,
The proof of Tchakaloff's theorem, Corollary 2 and Remark 2,
DOI 10.1090/S0002-9939-06-08249-9. The cardinality step uses Carathéodory.
-/

noncomputable section

open Set MeasureTheory MeasureTheory.Measure Filter
open scoped Topology BigOperators
set_option autoImplicit false

namespace D5.S3.Analytic.Convexity.PositivePairedPoissonCubature

/-- Coefficients at each of the two frequencies ±n; the zero coefficient is one. -/
def pairedMultiplier (D σ : ℝ) (n : ℕ) : ℝ :=
  ((1 / σ) ^ n + (D * σ) ^ n) / 2

def inverseCoeff (D σ : ℝ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n / pairedMultiplier D σ n

def weightedMass (σ : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ, |f (n + 1)| * σ ^ (n + 1)

/-- The coefficient at each of ±(n+1) contributes twice to real synthesis. -/
def cosineDensity (c : ℕ → ℝ) (θ : ℝ) : ℝ :=
  c 0 + 2 * ∑' n : ℕ, c (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ)

private lemma multiplier_pos {D σ : ℝ} (hD : 0 ≤ D) (hσ : 0 < σ) (n : ℕ) :
    0 < pairedMultiplier D σ n := by
  have hp := pow_pos (one_div_pos.mpr hσ) n
  have hd := pow_nonneg (mul_nonneg hD hσ.le) n
  unfold pairedMultiplier
  linarith

private lemma inverse_bound {D σ : ℝ} (hD : 0 ≤ D) (hσ : 0 < σ)
    (f : ℕ → ℝ) (n : ℕ) :
    |inverseCoeff D σ f n| ≤ 2 * (|f n| * σ ^ n) := by
  have hp := multiplier_pos hD hσ n
  have hl : (1 / σ) ^ n / 2 ≤ pairedMultiplier D σ n := by
    have hd := pow_nonneg (mul_nonneg hD hσ.le) n
    unfold pairedMultiplier
    linarith
  rw [inverseCoeff, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).2
  calc
    |f n| = (2 * (|f n| * σ ^ n)) * ((1 / σ) ^ n / 2) := by
      rw [div_pow]
      field_simp [ne_of_gt hσ]; ring
    _ ≤ (2 * (|f n| * σ ^ n)) * pairedMultiplier D σ n :=
      mul_le_mul_of_nonneg_left hl (by positivity)

private lemma cosine_term_bound (c : ℕ → ℝ) (n : ℕ) (θ : ℝ) :
    ‖c (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ)‖ ≤ |c (n + 1)| := by
  rw [Real.norm_eq_abs, abs_mul]
  simpa using mul_le_mul_of_nonneg_left
    (Real.abs_cos_le_one (((n + 1 : ℕ) : ℝ) * θ)) (abs_nonneg (c (n + 1)))

private lemma density_continuous {c : ℕ → ℝ}
    (hs : Summable (fun n => |c (n + 1)|)) : Continuous (cosineDensity c) := by
  unfold cosineDensity
  apply continuous_const.add
  apply continuous_const.mul
  exact continuous_tsum
    (fun n => continuous_const.mul
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
    hs (cosine_term_bound c)

private lemma density_even (c : ℕ → ℝ) (θ : ℝ) :
    cosineDensity c (-θ) = cosineDensity c θ := by
  simp only [cosineDensity, mul_neg, Real.cos_neg]

private lemma density_periodic (c : ℕ → ℝ) :
    Function.Periodic (cosineDensity c) (2 * Real.pi) := by
  intro θ
  simp only [cosineDensity, mul_add, Real.cos_add_nat_mul_two_pi]

private lemma density_deviation {c : ℕ → ℝ}
    (hs : Summable (fun n => |c (n + 1)|)) (θ : ℝ) :
    |cosineDensity c θ - c 0| ≤ 2 * ∑' n : ℕ, |c (n + 1)| := by
  have ht : |∑' n : ℕ, c (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ)| ≤
      ∑' n : ℕ, |c (n + 1)| := by
    simpa only [Real.norm_eq_abs] using
      tsum_of_norm_bounded hs.hasSum (fun n => cosine_term_bound c n θ)
  simpa only [cosineDensity, add_sub_cancel_left, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] using
    mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)

/-- Direct weighted inversion at radius 1/σ. Absolute membership and strict
positivity of the inverse are conclusions. The coefficient identity does not
assert the separate normalized-Haar/Bochner convolution bridge. -/
theorem weighted_positive_paired_poisson_inverse
    {D σ M : ℝ} {f : ℕ → ℝ}
    (hσ : 1 < σ) (hD : 0 ≤ D) (hpair : D * σ ^ 2 < 1)
    (hM : 0 < M) (hmean : f 0 = M)
    (hweighted : Summable (fun n : ℕ => |f (n + 1)| * σ ^ (n + 1)))
    (hsmall : 2 * weightedMass σ f ≤ M / 16) :
    Summable (fun n : ℕ => |pairedMultiplier D σ n|) ∧
    pairedMultiplier D σ 0 = 1 ∧
    (∀ n : ℕ, 0 < pairedMultiplier D σ n ∧
      pairedMultiplier D σ n ≤ (1 / σ) ^ n) ∧
    Summable (fun n : ℕ => |inverseCoeff D σ f n|) ∧
    inverseCoeff D σ f 0 = M ∧
    2 * (∑' n : ℕ, |inverseCoeff D σ f (n + 1)|) ≤ 4 * weightedMass σ f ∧
    4 * weightedMass σ f ≤ M / 8 ∧
    Continuous (cosineDensity (inverseCoeff D σ f)) ∧
    (∀ θ : ℝ, cosineDensity (inverseCoeff D σ f) (-θ) =
      cosineDensity (inverseCoeff D σ f) θ) ∧
    Function.Periodic (cosineDensity (inverseCoeff D σ f)) (2 * Real.pi) ∧
    (∀ θ : ℝ, M / 2 < cosineDensity (inverseCoeff D σ f) θ) ∧
    (∀ n : ℕ, pairedMultiplier D σ n * inverseCoeff D σ f n = f n) ∧
    (∀ θ : ℝ,
      cosineDensity (fun n => pairedMultiplier D σ n * inverseCoeff D σ f n) θ =
        cosineDensity f θ) := by
  have hσ0 : 0 < σ := lt_trans zero_lt_one hσ
  have ha0 : 0 < 1 / σ := one_div_pos.mpr hσ0
  have ha1 : 1 / σ < 1 := (div_lt_one hσ0).2 hσ
  have hd : D * σ ≤ 1 / σ := by
    apply (le_div_iff₀ hσ0).2
    nlinarith [hpair]
  have hkernel (n : ℕ) : 0 < pairedMultiplier D σ n ∧
      pairedMultiplier D σ n ≤ (1 / σ) ^ n := by
    refine ⟨multiplier_pos hD hσ0 n, ?_⟩
    have hp := pow_le_pow_left₀ (mul_nonneg hD hσ0.le) hd n
    unfold pairedMultiplier
    linarith
  have hks : Summable (fun n : ℕ => |pairedMultiplier D σ n|) := by
    apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun n => (abs_of_pos (hkernel n).1).le.trans (hkernel n).2)
    exact summable_geometric_of_lt_one ha0.le ha1
  have hit : Summable (fun n : ℕ => |inverseCoeff D σ f (n + 1)|) :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (fun n => inverse_bound hD hσ0 f (n + 1)) (hweighted.mul_left 2)
  have his : Summable (fun n : ℕ => |inverseCoeff D σ f n|) :=
    (summable_nat_add_iff 1).1 hit
  have hiz : inverseCoeff D σ f 0 = M := by
    simpa [inverseCoeff, pairedMultiplier] using hmean
  have hmass : 2 * (∑' n : ℕ, |inverseCoeff D σ f (n + 1)|) ≤
      4 * weightedMass σ f := by
    have hc := hit.tsum_le_tsum (fun n => inverse_bound hD hσ0 f (n + 1))
      (hweighted.mul_left 2)
    rw [tsum_mul_left] at hc
    unfold weightedMass
    linarith
  have hmassM : 4 * weightedMass σ f ≤ M / 8 := by linarith
  have hmul (n : ℕ) : pairedMultiplier D σ n * inverseCoeff D σ f n = f n := by
    unfold inverseCoeff
    field_simp [ne_of_gt (hkernel n).1]
  refine ⟨hks, by norm_num [pairedMultiplier], hkernel, his, hiz, hmass, hmassM,
    density_continuous hit, density_even _, density_periodic _, ?_, hmul, ?_⟩
  · intro θ
    have hb := (density_deviation hit θ).trans (hmass.trans hmassM)
    rw [hiz] at hb
    have hlo := (abs_le.mp hb).1
    linarith
  · intro θ
    rw [show (fun n => pairedMultiplier D σ n * inverseCoeff D σ f n) = f
      from funext hmul]

/-- Normalized real Haar integral in the angular coordinate. -/
def haarMean (g : ℝ → ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..2 * Real.pi, g θ

private lemma integral_cos_integer (n : ℤ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Real.cos ((n : ℝ) * θ)) =
      if n = 0 then 2 * Real.pi else 0 := by
  split_ifs with hn
  · subst n
    simp
  · rw [intervalIntegral.integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn),
      integral_cos]
    have hs : Real.sin ((n : ℝ) * (2 * Real.pi)) = 0 := by
      rw [show (n : ℝ) * (2 * Real.pi) = ((2 * n : ℤ) : ℝ) * Real.pi by push_cast; ring]
      exact Real.sin_int_mul_pi _
    simp [hs]

private lemma integral_cos_pos (n : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos (((n + 1 : ℕ) : ℝ) * θ)) = 0 := by
  have h := integral_cos_integer ((n : ℤ) + 1)
  rw [ite_eq_right (by omega : (n : ℤ) + 1 ≠ 0)] at h
  simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one] using h

private lemma integral_cos_orthogonal (n k : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      Real.cos (((n + 1 : ℕ) : ℝ) * θ) *
      Real.cos (((k + 1 : ℕ) : ℝ) * θ)) =
      if n = k then Real.pi else 0 := by
  have hp (θ : ℝ) :
      Real.cos (((n + 1 : ℕ) : ℝ) * θ) *
        Real.cos (((k + 1 : ℕ) : ℝ) * θ) =
      (Real.cos ((((n : ℤ) + 1 + (k + 1) : ℤ) : ℝ) * θ) +
        Real.cos ((((n : ℤ) + 1 - (k + 1) : ℤ) : ℝ) * θ)) / 2 := by
    push_cast
    rw [show ((n : ℝ) + 1 + (k + 1)) * θ =
      ((n : ℝ) + 1) * θ + ((k : ℝ) + 1) * θ by ring,
      show ((n : ℝ) + 1 - (k + 1)) * θ =
      ((n : ℝ) + 1) * θ - ((k : ℝ) + 1) * θ by ring,
      Real.cos_add, Real.cos_sub]
    ring
  simp_rw [hp]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop),
    integral_cos_integer, integral_cos_integer]
  have ha : (n : ℤ) + 1 + (k + 1) ≠ 0 := by omega
  by_cases h : n = k
  · subst k
    simp [ha]
  · have hb : (n : ℤ) + 1 - (k + 1) ≠ 0 := by omega
    simp only [ite_eq_right ha, ite_eq_right hb, ite_eq_right h, add_zero, zero_div]

/-- Uniform summable bounds justify the actual interval integral/series exchange. -/
private lemma integral_tsum_of_bound {F : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hc : ∀ n, Continuous (F n)) (hs : Summable b)
    (hb : ∀ n θ, ‖F n θ‖ ≤ b n) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, ∑' n : ℕ, F n θ) =
      ∑' n : ℕ, ∫ θ in (0 : ℝ)..2 * Real.pi, F n θ := by
  exact (intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun n _ => b n) (fun n => (hc n).aestronglyMeasurable)
    (fun n => ae_of_all _ (fun θ _ => hb n θ))
    (ae_of_all _ (fun _ _ => hs)) intervalIntegrable_const
    (ae_of_all _ (fun θ _ => (hs.of_norm_bounded (fun n => hb n θ)).hasSum))).tsum_eq.symm

private lemma integral_density {c : ℕ → ℝ}
    (hs : Summable (fun n => |c (n + 1)|)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, cosineDensity c θ) =
      (2 * Real.pi) * c 0 := by
  unfold cosineDensity
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (by apply Continuous.intervalIntegrable
        exact continuous_const.mul (by
          apply continuous_tsum
            (fun n => continuous_const.mul
              (Real.continuous_cos.comp (continuous_const.mul continuous_id)))
            hs (cosine_term_bound c))),
    intervalIntegral.integral_const_mul,
    integral_tsum_of_bound
      (fun n => by fun_prop) hs (cosine_term_bound c)]
  simp_rw [intervalIntegral.integral_const_mul, integral_cos_pos, mul_zero]
  simp [mul_comm]

private lemma cosine_product_term_bound (c : ℕ → ℝ) (n k : ℕ) (θ : ℝ) :
    ‖c (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) *
        Real.cos (((k + 1 : ℕ) : ℝ) * θ)‖ ≤ |c (n + 1)| := by
  rw [norm_mul]
  calc
    _ ≤ |c (n + 1)| * 1 := mul_le_mul
      (cosine_term_bound c n θ)
      (by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (((k + 1 : ℕ) : ℝ) * θ))
      (norm_nonneg _) (abs_nonneg _)
    _ = _ := mul_one _

private lemma integral_density_cos {c : ℕ → ℝ}
    (hs : Summable (fun n => |c (n + 1)|)) (k : ℕ) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      cosineDensity c θ * Real.cos (((k + 1 : ℕ) : ℝ) * θ)) =
      (2 * Real.pi) * c (k + 1) := by
  have he (θ : ℝ) : cosineDensity c θ * Real.cos (((k + 1 : ℕ) : ℝ) * θ) =
      c 0 * Real.cos (((k + 1 : ℕ) : ℝ) * θ) +
      2 * ∑' n : ℕ, c (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) *
        Real.cos (((k + 1 : ℕ) : ℝ) * θ) := by
    rw [cosineDensity, add_mul, mul_assoc, tsum_mul_right]
  simp_rw [he]
  rw [intervalIntegral.integral_add
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable
        exact continuous_const.mul (by
          apply continuous_tsum (fun n => by fun_prop) hs
            (fun n θ => cosine_product_term_bound c n k θ))),
    intervalIntegral.integral_const_mul, integral_cos_pos, mul_zero, zero_add,
    intervalIntegral.integral_const_mul,
    integral_tsum_of_bound (fun n => by fun_prop) hs
      (fun n θ => cosine_product_term_bound c n k θ)]
  have ht (n : ℕ) :
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        c (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) *
        Real.cos (((k + 1 : ℕ) : ℝ) * θ)) =
      if n = k then c (k + 1) * Real.pi else 0 := by
    rw [show (fun θ => c (n + 1) * Real.cos (((n + 1 : ℕ) : ℝ) * θ) *
      Real.cos (((k + 1 : ℕ) : ℝ) * θ)) =
      (fun θ => c (n + 1) * (Real.cos (((n + 1 : ℕ) : ℝ) * θ) *
      Real.cos (((k + 1 : ℕ) : ℝ) * θ))) from funext (fun _ => mul_assoc _ _ _)]
    rw [intervalIntegral.integral_const_mul, integral_cos_orthogonal]
    split_ifs with h
    · simp [h]
    · simp
  simp_rw [ht]
  rw [tsum_ite_eq]
  ring

/-- Mean and every positive cosine moment, obtained from the synthesis itself. -/
theorem cosineDensity_haar_moments {c : ℕ → ℝ}
    (hs : Summable (fun n : ℕ => |c n|)) :
    IntervalIntegrable (cosineDensity c) volume 0 (2 * Real.pi) ∧
    haarMean (cosineDensity c) = c 0 ∧
    ∀ k : ℕ, 0 < k →
      IntervalIntegrable (fun θ => cosineDensity c θ * Real.cos ((k : ℝ) * θ))
        volume 0 (2 * Real.pi) ∧
      haarMean (fun θ => cosineDensity c θ * Real.cos ((k : ℝ) * θ)) = c k := by
  have ht : Summable (fun n : ℕ => |c (n + 1)|) := (summable_nat_add_iff 1).2 hs
  have hc := density_continuous ht
  refine ⟨hc.intervalIntegrable _ _, ?_, ?_⟩
  · rw [haarMean, integral_density ht]
    field_simp
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    refine ⟨(hc.mul (by fun_prop)).intervalIntegrable _ _, ?_⟩
    rw [haarMean, integral_density_cos ht]
    field_simp

/-- Normalize the actual continuous positive interval density.  The second
conclusion is the change-of-density formula, including its normalization. -/
private theorem cubature_interval_probability {ρ : ℝ → ℝ} {M : ℝ}
    (hM : 0 < M) (hc : Continuous ρ) (hp : ∀ θ, 0 ≤ ρ θ)
    (hm : haarMean ρ = M) :
    let μ : Measure ℝ := (volume.restrict (Ioc 0 (2 * Real.pi))).withDensity
      (fun θ => ENNReal.ofReal (((1 / (2 * Real.pi)) / M) * ρ θ))
    IsProbabilityMeasure μ ∧
      ∀ g : ℝ → ℝ, (∫ θ, g θ ∂μ) = haarMean (fun θ => ρ θ * g θ) / M := by
  let a : ℝ := (1 / (2 * Real.pi)) / M
  let q : ℝ → ℝ := fun θ => a * ρ θ
  let μ : Measure ℝ := (volume.restrict (Ioc 0 (2 * Real.pi))).withDensity
    (fun θ => ENNReal.ofReal (q θ))
  change IsProbabilityMeasure μ ∧ _
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hq : ∀ θ, 0 ≤ q θ := fun θ => mul_nonneg ha (hp θ)
  have hqc : Continuous q := continuous_const.mul hc
  have hqi : Integrable q (volume.restrict (Ioc 0 (2 * Real.pi))) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp
      (hqc.intervalIntegrable _ _)
  have hqmass : (∫ θ in Ioc 0 (2 * Real.pi), q θ) = 1 := by
    change (∫ θ in Ioc 0 (2 * Real.pi), a * ρ θ) = 1
    rw [integral_const_mul,
      ← intervalIntegral.integral_of_le Real.two_pi_pos.le]
    calc
      a * (∫ θ in (0 : ℝ)..2 * Real.pi, ρ θ) = haarMean ρ / M := by
        dsimp [a, haarMean]
        ring
      _ = 1 := by rw [hm, div_self (ne_of_gt hM)]
  have hμmass : μ univ = 1 := by
    change ((volume.restrict (Ioc 0 (2 * Real.pi))).withDensity
      (fun θ => ENNReal.ofReal (q θ))) univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hqi (ae_of_all _ hq), hqmass,
      ENNReal.ofReal_one]
  refine ⟨⟨hμmass⟩, ?_⟩
  intro g
  change (∫ θ, g θ ∂(volume.restrict (Ioc 0 (2 * Real.pi))).withDensity
    (fun θ => ENNReal.ofReal (q θ))) = haarMean (fun θ => ρ θ * g θ) / M
  rw [integral_withDensity_eq_integral_toReal_smul hqc.measurable.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (hq _), smul_eq_mul]
  change (∫ θ in Ioc 0 (2 * Real.pi), (a * ρ θ) * g θ) =
    haarMean (fun θ => ρ θ * g θ) / M
  simp_rw [mul_assoc]
  rw [integral_const_mul,
    ← intervalIntegral.integral_of_le Real.two_pi_pos.le]
  dsimp [a, haarMean]
  ring

/-- Apply the actual-hull supplier and retain Carathéodory's affine independence
until after bounding the number of atoms in the L-dimensional moment carrier. -/
private theorem cubature_bounded_probability {α : Type*} [MeasurableSpace α]
    (L : ℕ) (μ : Measure α) [IsProbabilityMeasure μ]
    {g : α → (Fin L → ℝ)} (hgi : Integrable g μ) :
    ∃ J : ℕ, 1 ≤ J ∧ J ≤ L + 1 ∧
      ∃ (p : Fin J → ℝ) (a : Fin J → α),
        (∀ j, 0 < p j) ∧ (∑ j, p j = 1) ∧
          (∑ j, p j • g (a j)) = ∫ x, g x ∂μ := by
  classical
  have hmem :=
    D5.S3.Analytic.Convexity.MeasurableFiniteMoments.integral_mem_convexHull μ hgi
  obtain ⟨ι, hι, z, w, hz, haff, hw, hw1, hwe⟩ :=
    eq_pos_convex_span_of_mem_convexHull hmem
  letI : Fintype ι := hι
  have hcard : Fintype.card ι ≤ L + 1 := by
    calc
      Fintype.card ι ≤ Module.finrank ℝ (vectorSpan ℝ (range z)) + 1 :=
        haff.card_le_finrank_succ
      _ ≤ Module.finrank ℝ (Fin L → ℝ) + 1 :=
        Nat.add_le_add_right (Submodule.finrank_le _) 1
      _ = L + 1 := by rw [Module.finrank_pi]; simp
  have hnonempty : 1 ≤ Fintype.card ι := by
    by_contra h
    have hzero : Fintype.card ι = 0 := by omega
    letI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hzero
    have hbad : (0 : ℝ) = 1 := by simpa using hw1
    norm_num at hbad
  have hx (i : ι) : ∃ a : α, g a = z i := hz (mem_range_self i)
  choose a ha using hx
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, hnonempty, hcard, w ∘ e, a ∘ e,
    (fun j => hw (e j)), ?_, ?_⟩
  · simpa only [Function.comp_def] using (e.sum_comp w).trans hw1
  · have hs : (∑ i : ι, w i • g (a i)) = ∫ x, g x ∂μ := by
      calc
        (∑ i : ι, w i • g (a i)) = ∑ i : ι, w i • z i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [ha i]
        _ = _ := hwe
    simpa only [Function.comp_def] using
      (e.sum_comp (fun i => w i • g (a i))).trans hs

/-- Actual finite positive cosine cubature for every initial segment of the
weighted input.  The density and its probability normalization are constructed
inside the proof.  No sign restriction is placed on the positive-index data. -/
theorem weighted_positive_paired_poisson_finite_cubature
    {D σ M : ℝ} {f : ℕ → ℝ}
    (hσ : 1 < σ) (hD : 0 ≤ D) (hpair : D * σ ^ 2 < 1)
    (hM : 0 < M) (hmean : f 0 = M)
    (hweighted : Summable (fun n : ℕ => |f (n + 1)| * σ ^ (n + 1)))
    (hsmall : 2 * weightedMass σ f ≤ M / 16) (L : ℕ) :
    ∃ J : ℕ, 1 ≤ J ∧ J ≤ L + 1 ∧
      ∃ (t : Fin J → ℝ) (θ : Fin J → ℝ),
        (∀ j, 0 ≤ t j) ∧ (∑ j, t j = M / 2) ∧
        (∀ j, θ j ∈ Icc 0 (2 * Real.pi)) ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ L →
          (∑ j, t j * pairedMultiplier D σ k * Real.cos ((k : ℝ) * θ j)) =
            f k / 2 := by
  classical
  obtain ⟨_, _, _, his, hiz, _, _, hc, _, _, hp, hmul, _⟩ :=
    weighted_positive_paired_poisson_inverse hσ hD hpair hM hmean hweighted hsmall
  obtain ⟨_, hmass, hcos⟩ := cosineDensity_haar_moments his
  let ρ : ℝ → ℝ := cosineDensity (inverseCoeff D σ f)
  have hρ : Continuous ρ := hc
  have hρpos : ∀ x, 0 ≤ ρ x := by
    intro x
    have h := hp x
    change M / 2 < ρ x at h
    linarith
  have hρmass : haarMean ρ = M := hmass.trans hiz
  let μ : Measure ℝ := (volume.restrict (Ioc 0 (2 * Real.pi))).withDensity
    (fun x => ENNReal.ofReal (((1 / (2 * Real.pi)) / M) * ρ x))
  obtain ⟨hprob, hchange⟩ := cubature_interval_probability hM hρ hρpos hρmass
  letI : IsProbabilityMeasure μ := hprob
  let phase : ℝ → ℝ := fun x => max 0 (min (2 * Real.pi) x)
  have hphase (x : ℝ) : phase x ∈ Icc 0 (2 * Real.pi) := by
    exact ⟨le_max_left _ _, max_le Real.two_pi_pos.le (min_le_left _ _)⟩
  have hphase_eq (x : ℝ) (hx : x ∈ Ioc 0 (2 * Real.pi)) : phase x = x := by
    dsimp [phase]
    rw [min_eq_right hx.2, max_eq_right hx.1.le]
  have hphase_cont : Continuous phase :=
    continuous_const.max (continuous_const.min continuous_id)
  let g : ℝ → (Fin L → ℝ) :=
    fun x i => Real.cos (((i.val + 1 : ℕ) : ℝ) * phase x)
  have hgc : Continuous g := continuous_pi (fun i =>
    Real.continuous_cos.comp (continuous_const.mul hphase_cont))
  have hgi : Integrable g μ := by
    apply (integrable_const (1 : ℝ)).mono' hgc.aestronglyMeasurable
    apply ae_of_all
    intro x
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
    intro i
    simpa only [g, Real.norm_eq_abs] using
      Real.abs_cos_le_one (((i.val + 1 : ℕ) : ℝ) * phase x)
  have hmoment (i : Fin L) :
      (∫ x, g x ∂μ) i = inverseCoeff D σ f (i.val + 1) / M := by
    have hproj := (ContinuousLinearMap.proj i : (Fin L → ℝ) →L[ℝ] ℝ).integral_comp_comm hgi
    change (∫ x, g x i ∂μ) = (∫ x, g x ∂μ) i at hproj
    have hraw : haarMean (fun x => ρ x * g x i) =
        haarMean (fun x => ρ x * Real.cos (((i.val + 1 : ℕ) : ℝ) * x)) := by
      unfold haarMean
      apply congrArg (fun v : ℝ => (1 / (2 * Real.pi)) * v)
      rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
        intervalIntegral.integral_of_le Real.two_pi_pos.le]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      dsimp only [g]
      rw [hphase_eq x hx]
    calc
      (∫ x, g x ∂μ) i = ∫ x, g x i ∂μ := hproj.symm
      _ = haarMean (fun x => ρ x * g x i) / M := hchange _
      _ = haarMean (fun x => ρ x * Real.cos (((i.val + 1 : ℕ) : ℝ) * x)) / M :=
        congrArg (fun v : ℝ => v / M) hraw
      _ = inverseCoeff D σ f (i.val + 1) / M := by
        rw [(hcos (i.val + 1) (by omega)).2]
  obtain ⟨J, hJpos, hJle, p, a, hp, hpsum, hpeval⟩ :=
    cubature_bounded_probability L μ hgi
  let t : Fin J → ℝ := fun j => (M / 2) * p j
  let θ : Fin J → ℝ := fun j => phase (a j)
  refine ⟨J, hJpos, hJle, t, θ, ?_, ?_, (fun j => hphase (a j)), ?_⟩
  · intro j
    exact mul_nonneg (by positivity) (hp j).le
  · change (∑ j, (M / 2) * p j) = M / 2
    rw [← Finset.mul_sum, hpsum, mul_one]
  · intro k hk hkle
    let i : Fin L := ⟨k - 1, by omega⟩
    have hik : i.val + 1 = k := by dsimp [i]; omega
    have hmoment_sum : (∑ j, p j * Real.cos ((k : ℝ) * θ j)) =
        inverseCoeff D σ f k / M := by
      have he := (congrFun hpeval i).trans (hmoment i)
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, g, θ, hik] using he
    calc
      (∑ j, t j * pairedMultiplier D σ k * Real.cos ((k : ℝ) * θ j)) =
          ((M / 2) * pairedMultiplier D σ k) *
            (∑ j, p j * Real.cos ((k : ℝ) * θ j)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        dsimp [t]
        ring
      _ = ((M / 2) * pairedMultiplier D σ k) * (inverseCoeff D σ f k / M) := by
        rw [hmoment_sum]
      _ = (pairedMultiplier D σ k * inverseCoeff D σ f k) / 2 := by
        field_simp [ne_of_gt hM]
        <;> ring
      _ = f k / 2 := by rw [hmul k]

end D5.S3.Analytic.Convexity.PositivePairedPoissonCubature
