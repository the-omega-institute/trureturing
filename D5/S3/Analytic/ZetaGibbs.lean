/- GID: D5/S3/Analytic/ZetaGibbs
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The zeta distribution is the Gibbs measure for logarithmic integer energy. -/

import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace D5.S3.Analytic.ZetaGibbs

open scoped ENNReal

noncomputable section

/-- The Boltzmann weight for logarithmic energy on the positive integers. -/
def weight (s : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((n : ℝ) ^ (-s))

/-- The zero slot has no mass at positive inverse temperature. -/
@[simp] theorem weight_zero (s : ℝ) (hs : 0 < s) : weight s 0 = 0 := by
  simp [weight, Real.zero_rpow (neg_ne_zero.mpr hs.ne')]

/-- The unit-energy slot has weight one. -/
@[simp] theorem weight_one (s : ℝ) : weight s 1 = 1 := by
  simp [weight]

/-- The partition function of the logarithmic integer ensemble. -/
def partitionFunction (s : ℝ) : ℝ≥0∞ :=
  ∑' n : ℕ, weight s n

/-- The underlying real p-series is summable above inverse temperature one. -/
theorem summable_real_weight (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-s)) := by
  rw [Real.summable_nat_rpow]
  linarith

/-- Above inverse temperature one, the partition function is finite. -/
theorem partition_function_ne_top (s : ℝ) (hs : 1 < s) : partitionFunction s ≠ ∞ := by
  exact (summable_real_weight s hs).tsum_ofReal_ne_top

/-- The partition function is positive at every inverse temperature. -/
theorem partition_function_pos (s : ℝ) : 0 < partitionFunction s := by
  calc
    0 < weight s 1 := by simp
    _ ≤ partitionFunction s := ENNReal.le_tsum 1

/-- The partition function is nonzero at every inverse temperature. -/
theorem partition_function_ne_zero (s : ℝ) : partitionFunction s ≠ 0 :=
  (partition_function_pos s).ne'

/-- The zeta distribution, obtained by normalizing logarithmic Boltzmann weights. -/
def zetaDist (s : ℝ) (hs : 1 < s) : PMF ℕ :=
  PMF.normalize (weight s) (partition_function_ne_zero s) (partition_function_ne_top s hs)

/-- Pointwise Gibbs formula for the zeta distribution. -/
theorem zeta_dist_apply (s : ℝ) (hs : 1 < s) (n : ℕ) :
    zetaDist s hs n = weight s n * (∑' m : ℕ, weight s m)⁻¹ := by
  exact PMF.normalize_apply (partition_function_ne_zero s) (partition_function_ne_top s hs) n

/-- The finite ENNReal partition function is the real Riemann zeta value. -/
theorem partition_function_toReal_eq_riemannZeta (s : ℝ) (hs : 1 < s) :
    ((partitionFunction s).toReal : ℂ) = riemannZeta (s : ℂ) := by
  have hsum := summable_real_weight s hs
  have hnonneg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-s) :=
    fun n => Real.rpow_nonneg n.cast_nonneg _
  change ((∑' n : ℕ, ENNReal.ofReal ((n : ℝ) ^ (-s))).toReal : ℂ) = riemannZeta (s : ℂ)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum,
    ENNReal.toReal_ofReal (tsum_nonneg hnonneg), Complex.ofReal_tsum,
    zeta_eq_tsum_one_div_nat_cpow (by simpa using hs)]
  apply tsum_congr
  intro n
  rw [Complex.ofReal_cpow n.cast_nonneg]
  simp only [Complex.ofReal_neg, Complex.ofReal_natCast, Complex.cpow_neg, one_div]

/-- Forcing check: at inverse temperature one the ENNReal partition function is infinite. -/
theorem weight_one_tsum_eq_top :
    ∑' n : ℕ, weight 1 n = ∞ := by
  simp only [weight, ENNReal.ofReal]
  rw [ENNReal.tsum_coe_eq_top_iff_not_summable_coe]
  have hdiv : ¬Summable (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) := by
    rw [Real.summable_nat_rpow]
    norm_num
  simp [Real.rpow_nonneg, hdiv]

end

end D5.S3.Analytic.ZetaGibbs
