/- GID: D5/S3/Analytic/PetzCothStripMode
   generality: G
   mirror-B: D5/B/S3/Analytic/PetzCothStripMode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coth evaluation of the compensated lower Poisson mode. -/

import D5.S3.Analytic.CothBernoulliDegree.PartialFraction
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# The lower Poisson weight on a single strip mode

The lower boundary density is the width-one-half specialization in Yang,
*Quantum data processing equality*, arXiv:2609.33815v2, §III.1, Eq. (III.2). Its positive-ray
exponential expansion gives a summable family of compensated Laplace integrals.
The frozen hyperbolic cotangent partial fraction and reflection evaluate the result.
-/

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace PetzCothStripMode

noncomputable section

/-- The lower-boundary Poisson weight for the strip of width one half.
The value at the single point `0` is given by Lean's total division. -/
def lowerWeight (s : ℝ) : ℝ := Real.pi / (Real.cosh (2 * Real.pi * s) - 1)

/-- The exponential rate for the positive integer `k + 1`. -/
private def decayRate (k : ℕ) : ℝ := 2 * Real.pi * ((k : ℝ) + 1)

/-- The lower weight compensated by the cosine deficit at frequency `ω`. -/
def lowerMode (ω s : ℝ) : ℝ := lowerWeight s * (1 - Real.cos (ω * s))

private def lowerTerm (ω : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  decayRate k * (Real.exp (-(decayRate k) * s) * (1 - Real.cos (ω * s)))

private theorem decayRate_pos (k : ℕ) : 0 < decayRate k := by
  unfold decayRate
  positivity

set_option maxHeartbeats 1000000 in
-- Normalizing the exponential series requires several real power identities.
/-- Exact positive expansion of the actual lower weight on `s > 0`. -/
private theorem lowerWeight_hasSum {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : ℕ => decayRate k * Real.exp (-(decayRate k) * s)) (lowerWeight s) := by
  let x : ℝ := 2 * Real.pi * s
  let r : ℝ := Real.exp (-x)
  have hx : 0 < x := by dsimp [x]; positivity
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr hx)
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_pos hr0] using hr1
  have hseries : HasSum (fun k : ℕ => (k : ℝ) * r ^ k) (r / (1 - r) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (r := r) hr
  rw [← hasSum_nat_add_iff' 1] at hseries
  have hgeom : HasSum (fun k : ℕ => ((k : ℝ) + 1) * r ^ (k + 1)) (r / (1 - r) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, Finset.sum_range_one, Nat.cast_zero, zero_mul,
      sub_zero] using hseries
  have hrecip : Real.exp x * r = 1 := by
    dsimp [r]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hcosh : (Real.cosh x - 1) * (2 * r) = (1 - r) ^ 2 := by
    rw [Real.cosh_eq, show Real.exp (-x) = r from rfl]
    calc
      _ = Real.exp x * r + r ^ 2 - 2 * r := by ring
      _ = _ := by rw [hrecip]; ring
  have hden : Real.cosh x - 1 ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hcosh
    exact (pow_ne_zero 2 (sub_ne_zero.mpr hr1.ne')) hcosh.symm
  have hvalue : (2 * Real.pi) * (r / (1 - r) ^ 2) = lowerWeight s := by
    change (2 * Real.pi) * (r / (1 - r) ^ 2) = Real.pi / (Real.cosh x - 1)
    rw [← hcosh]
    field_simp [hden, hr0.ne'] <;> ring
  rw [← hvalue]
  refine (hgeom.mul_left (2 * Real.pi)).congr_fun fun k => ?_
  have hexponent : -(decayRate k) * s = ((k + 1 : ℕ) : ℝ) * (-x) := by
    simp only [decayRate, x, Nat.cast_add, Nat.cast_one]
    ring
  rw [hexponent, Real.exp_nat_mul]
  change (2 * Real.pi * ((k : ℝ) + 1)) * r ^ (k + 1) =
    (2 * Real.pi) * (((k : ℝ) + 1) * r ^ (k + 1))
  exact mul_assoc _ _ _

private theorem lowerTerm_nonneg (ω : ℝ) (k : ℕ) (s : ℝ) : 0 ≤ lowerTerm ω k s :=
  mul_nonneg (decayRate_pos k).le
    (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.cos_le_one _)))

/-- The compensated lower weight has the same expansion multiplied by `1 - cos (ωs)`. -/
private theorem lowerMode_hasSum (ω : ℝ) {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : ℕ => lowerTerm ω k s) (lowerMode ω s) := by
  simpa only [lowerMode, lowerTerm, mul_assoc] using
    (lowerWeight_hasSum hs).mul_right (1 - Real.cos (ω * s))

private theorem continuous_lowerTerm (ω : ℝ) (k : ℕ) : Continuous (lowerTerm ω k) := by
  unfold lowerTerm
  fun_prop

private theorem laplace_one_sub_cos {a : ℝ} (ha : 0 < a) (ω : ℝ) :
    IntegrableOn (fun s : ℝ => a * (Real.exp (-a * s) * (1 - Real.cos (ω * s)))) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, a * (Real.exp (-a * s) * (1 - Real.cos (ω * s)))) =
        ω ^ 2 / (a ^ 2 + ω ^ 2) := by
  have hexp := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
  have hcomp : IntegrableOn
      (fun s : ℝ => Real.exp (-a * s) * (1 - Real.cos (ω * s))) (Ioi 0) := by
    refine hexp.mul_bdd (c := 2) (by fun_prop) ?_
    filter_upwards with s
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (Real.cos_le_one _))]
    linarith only [Real.neg_one_le_cos (ω * s)]
  refine ⟨hcomp.const_mul a, ?_⟩
  rw [show (fun s : ℝ => a * (Real.exp (-a * s) * (1 - Real.cos (ω * s)))) =
      (fun s : ℝ => (a / 2) * (2 * Real.exp (-a * s) * (1 - Real.cos (ω * s)))) by
        funext s
        ring,
    integral_const_mul,
    D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition.integral_exp_neg_mul_one_sub_cos ha]
  have hden : a ^ 2 + ω ^ 2 ≠ 0 := by positivity
  field_simp [ha.ne', hden] <;> ring

private theorem integrableOn_lowerTerm (ω : ℝ) (k : ℕ) : IntegrableOn (lowerTerm ω k) (Ioi 0) :=
  (laplace_one_sub_cos (decayRate_pos k) ω).1

/-- The integral of the `k + 1` exponential term after multiplication by `1 - cos (ωs)`. -/
private theorem integral_lowerTerm (ω : ℝ) (k : ℕ) :
    (∫ s in Ioi 0, lowerTerm ω k s) = ω ^ 2 / (decayRate k ^ 2 + ω ^ 2) :=
  (laplace_one_sub_cos (decayRate_pos k) ω).2

private theorem summable_lowerCoefficients (ω : ℝ) :
    Summable (fun k : ℕ => ω ^ 2 / (decayRate k ^ 2 + ω ^ 2)) := by
  have hp : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < (2 : ℕ)))
  refine Summable.of_nonneg_of_le (f := fun k : ℕ =>
    (ω ^ 2 / (2 * Real.pi) ^ 2) * (1 / ((k : ℝ) + 1) ^ 2)) ?_ ?_ (hp.mul_left _)
  · intro k
    positivity
  · intro k
    calc
      _ ≤ ω ^ 2 / decayRate k ^ 2 := by
        apply div_le_div_of_nonneg_left (sq_nonneg ω) (pow_pos (decayRate_pos k) 2)
        exact le_add_of_nonneg_right (sq_nonneg ω)
      _ = _ := by simp only [decayRate, mul_pow, mul_one_div, div_div]

private theorem summable_integral_lowerTerm (ω : ℝ) :
    Summable (fun k : ℕ => ∫ s in Ioi 0, lowerTerm ω k s) := by
  simpa only [integral_lowerTerm] using summable_lowerCoefficients ω

/-- The sum of the integrals is the integral of the actual compensated lower weight. -/
private theorem integral_Ioi_lowerMode_eq_tsum (ω : ℝ) :
    (∫ s in Ioi 0, lowerMode ω s) = ∑' k : ℕ, ω ^ 2 / (decayRate k ^ 2 + ω ^ 2) := by
  have hnorm (k : ℕ) (s : ℝ) : ‖lowerTerm ω k s‖ = lowerTerm ω k s :=
    Real.norm_of_nonneg (lowerTerm_nonneg ω k s)
  have hsum : Summable (fun k : ℕ => ∫ s in Ioi 0, ‖lowerTerm ω k s‖) := by
    simpa only [hnorm] using summable_integral_lowerTerm ω
  calc
    _ = ∫ s in Ioi 0, ∑' k : ℕ, lowerTerm ω k s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      exact (lowerMode_hasSum ω hs).tsum_eq.symm
    _ = ∑' k : ℕ, ∫ s in Ioi 0, lowerTerm ω k s :=
      (integral_tsum_of_summable_integral_norm (integrableOn_lowerTerm ω) hsum).symm
    _ = _ := by simp only [integral_lowerTerm]

private theorem lowerMode_nonneg (ω s : ℝ) : 0 ≤ lowerMode ω s :=
  mul_nonneg (div_nonneg Real.pi_pos.le (sub_nonneg.mpr (Real.one_le_cosh _)))
    (sub_nonneg.mpr (Real.cos_le_one _))

/-- The positive-ray integral is absolutely convergent at every real frequency. -/
private theorem integrableOn_lowerMode (ω : ℝ) : IntegrableOn (lowerMode ω) (Ioi 0) := by
  have hm : Measurable (lowerMode ω) := by
    have hden : Continuous (fun s : ℝ => Real.cosh (2 * Real.pi * s) - 1) := by fun_prop
    have hcos : Continuous (fun s : ℝ => 1 - Real.cos (ω * s)) := by fun_prop
    exact (measurable_const.div hden.measurable).mul hcos.measurable
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (lowerMode_nonneg ω))]
  have heq : (fun s : ℝ => ENNReal.ofReal (lowerMode ω s)) =ᵐ[volume.restrict (Ioi 0)]
      (fun s : ℝ => ∑' k : ℕ, ENNReal.ofReal (lowerTerm ω k s)) := by
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
      with s hs
    have h := lowerMode_hasSum ω hs
    rw [← h.tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (fun k => lowerTerm_nonneg ω k s) h.summable
  have hterm (k : ℕ) :
      (∫⁻ s in Ioi 0, ENNReal.ofReal (lowerTerm ω k s)) =
        ENNReal.ofReal (∫ s in Ioi 0, lowerTerm ω k s) :=
    (ofReal_integral_eq_lintegral_ofReal (integrableOn_lowerTerm ω k)
      (Filter.Eventually.of_forall (lowerTerm_nonneg ω k))).symm
  rw [lintegral_congr_ae heq,
    lintegral_tsum (fun k => (continuous_lowerTerm ω k).measurable.ennreal_ofReal.aemeasurable)]
  simp_rw [hterm]
  exact (summable_integral_lowerTerm ω).tsum_ofReal_lt_top

private theorem integral_Ioi_lowerMode_of_pos {ω : ℝ} (hω : 0 < ω) :
    (∫ s in Ioi 0, lowerMode ω s) =
      ((ω / 2) * (Real.cosh (ω / 2) / Real.sinh (ω / 2)) - 1) / 2 := by
  let x : ℝ := ω / 2
  have hx : 0 < x := div_pos hω (by norm_num)
  have hωx : ω = 2 * x := by dsimp [x]; ring
  open D5.S3.Analytic.CothBernoulliDegree.Defs in
  have hseries :
      Real.cosh x / Real.sinh x / x - x ^ (-2 : ℤ) =
        2 * ∑' k : ℕ, 1 / (x ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2) := by
    simpa [P, p, Finset.sum_range_one] using
      D5.S3.Analytic.CothBernoulliDegree.PartialFraction.P_eq_tsum 0 0 hx
  have hterm (k : ℕ) :
      ω ^ 2 / (decayRate k ^ 2 + ω ^ 2) =
        x ^ 2 * (1 / (x ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2)) := by
    let b : ℝ := Real.pi * ((k : ℝ) + 1)
    have hrate : decayRate k = 2 * b := by
      dsimp [decayRate, b]
      ring
    have hden : x ^ 2 + b ^ 2 ≠ 0 := by positivity
    change ω ^ 2 / (decayRate k ^ 2 + ω ^ 2) = x ^ 2 * (1 / (x ^ 2 + b ^ 2))
    rw [hrate, hωx, show (2 * b) ^ 2 + (2 * x) ^ 2 = 4 * (x ^ 2 + b ^ 2) by ring]
    field_simp [hden] <;> ring
  have hvalue : x ^ 2 / 2 * (Real.cosh x / Real.sinh x / x - x ^ (-2 : ℤ)) =
      (x * (Real.cosh x / Real.sinh x) - 1) / 2 := by
    have hsh : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
    simp only [zpow_neg, zpow_ofNat]
    field_simp [hx.ne', hsh] <;> ring
  rw [← hvalue, integral_Ioi_lowerMode_eq_tsum, hseries]
  simp_rw [hterm]
  rw [tsum_mul_left]
  ring

private theorem lowerMode_neg_frequency (ω s : ℝ) : lowerMode (-ω) s = lowerMode ω s := by
  simp only [lowerMode, neg_mul, Real.cos_neg]

/-- The positive-ray integral is half the coth expression at any nonzero frequency. -/
private theorem integral_Ioi_lowerMode_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) :
    (∫ s in Ioi 0, lowerMode ω s) =
      ((ω / 2) * (Real.cosh (ω / 2) / Real.sinh (ω / 2)) - 1) / 2 := by
  rcases lt_or_gt_of_ne hω with hneg | hpos
  · simpa only [lowerMode_neg_frequency, neg_div, Real.cosh_neg, Real.sinh_neg, div_neg,
      neg_mul_neg] using integral_Ioi_lowerMode_of_pos (neg_pos.mpr hneg)
  · exact integral_Ioi_lowerMode_of_pos hpos

private theorem lowerMode_neg (ω s : ℝ) : lowerMode ω (-s) = lowerMode ω s := by
  simp only [lowerMode, lowerWeight, mul_neg, Real.cosh_neg, Real.cos_neg]

private theorem lowerMode_abs (ω s : ℝ) : lowerMode ω |s| = lowerMode ω s := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
  · rw [abs_of_nonpos hs, lowerMode_neg]

set_option maxHeartbeats 1000000 in
-- Elaborating the reflected restricted-measure integral requires extra heartbeats.
/-- The compensated lower weight is integrable on the full real line. -/
private theorem integrable_lowerMode (ω : ℝ) : Integrable (lowerMode ω) := by
  have hIoi : IntegrableOn (lowerMode ω) (Ioi 0) := integrableOn_lowerMode ω
  have hIic : IntegrableOn (lowerMode ω) (Iic 0) := by
    rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
    simp only [Function.comp_def, neg_preimage, neg_Iic, neg_zero, lowerMode_neg]
    exact (integrableOn_Ici_iff_integrableOn_Ioi (f := lowerMode ω)
      (b := (0 : ℝ)) (by finiteness)).2 hIoi
  have hUnion : IntegrableOn (lowerMode ω) (Iic 0 ∪ Ioi 0) := hIic.union hIoi
  rw [Iic_union_Ioi, integrableOn_univ] at hUnion
  exact hUnion

private theorem integral_lowerMode_eq_two_mul_Ioi (ω : ℝ) :
    (∫ s, lowerMode ω s) = 2 * ∫ s in Ioi 0, lowerMode ω s := by
  simpa only [lowerMode_abs] using (integral_comp_abs (f := lowerMode ω))

/-- The full lower-boundary mode integral at a nonzero real frequency. -/
private theorem integral_lowerMode_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) :
    (∫ s, lowerMode ω s) = (ω / 2) * (Real.cosh (ω / 2) / Real.sinh (ω / 2)) - 1 := by
  rw [integral_lowerMode_eq_two_mul_Ioi, integral_Ioi_lowerMode_of_ne_zero hω]
  ring

@[simp] private theorem lowerMode_zero (s : ℝ) : lowerMode 0 s = 0 := by
  simp [lowerMode]

/-- The whole-line coth formula with the zero-frequency branch. -/
theorem integral_lowerMode (ω : ℝ) :
    Integrable (lowerMode ω) ∧
      (∫ s, lowerMode ω s) =
        if ω = 0 then 0 else (ω / 2) * (Real.cosh (ω / 2) / Real.sinh (ω / 2)) - 1 := by
  refine ⟨integrable_lowerMode ω, ?_⟩
  by_cases hω : ω = 0
  · subst ω
    simp
  · rw [ite_eq_right hω]
    exact integral_lowerMode_of_ne_zero hω

end

end PetzCothStripMode
