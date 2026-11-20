import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
# The lower Poisson weight on a single strip mode

The lower weight is expanded on the positive ray. The individual Laplace integrals
are summable there, and reflection gives the whole-line coth formula.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace PetzCothStripMode

noncomputable section

/-- The lower-boundary Poisson weight for the strip of width one half.
The value at the single point `0` is given by Lean's total division. -/
def lowerWeight (s : ℝ) : ℝ := Real.pi / (Real.cosh (2 * Real.pi * s) - 1)

/-- The exponential rate for the positive integer `k + 1`. -/
def decayRate (k : ℕ) : ℝ := 2 * Real.pi * ((k : ℝ) + 1)

def lowerMode (ω s : ℝ) : ℝ := lowerWeight s * (1 - Real.cos (ω * s))

def lowerTerm (ω : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  decayRate k * (Real.exp (-(decayRate k) * s) * (1 - Real.cos (ω * s)))

private theorem decayRate_pos (k : ℕ) : 0 < decayRate k := by
  unfold decayRate
  positivity

set_option maxHeartbeats 1000000 in
/-- Exact positive expansion of the actual lower weight on `s > 0`. -/
theorem lowerWeight_hasSum {s : ℝ} (hs : 0 < s) :
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

theorem lowerWeight_eq_two_pi_mul_tsum {s : ℝ} (hs : 0 < s) :
    lowerWeight s = (2 * Real.pi) *
      ∑' k : ℕ, ((k : ℝ) + 1) * Real.exp (-(decayRate k) * s) := by
  rw [← (lowerWeight_hasSum hs).tsum_eq, ← tsum_mul_left]
  simp only [decayRate, mul_assoc]

theorem lowerTerm_nonneg (ω : ℝ) (k : ℕ) (s : ℝ) : 0 ≤ lowerTerm ω k s :=
  mul_nonneg (decayRate_pos k).le
    (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (Real.cos_le_one _)))

/-- The compensated lower weight has the same expansion multiplied by `1 - cos (ωs)`. -/
theorem lowerMode_hasSum (ω : ℝ) {s : ℝ} (hs : 0 < s) :
    HasSum (fun k : ℕ => lowerTerm ω k s) (lowerMode ω s) := by
  simpa only [lowerMode, lowerTerm, mul_assoc] using
    (lowerWeight_hasSum hs).mul_right (1 - Real.cos (ω * s))

private theorem continuous_lowerTerm (ω : ℝ) (k : ℕ) : Continuous (lowerTerm ω k) := by
  unfold lowerTerm
  fun_prop

private theorem laplace_cos {a : ℝ} (ha : 0 < a) (ω : ℝ) :
    IntegrableOn (fun s : ℝ => Real.exp (-a * s) * Real.cos (ω * s)) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, Real.exp (-a * s) * Real.cos (ω * s)) = a / (a ^ 2 + ω ^ 2) := by
  let z : ℂ := -(a : ℂ) + (ω : ℂ) * Complex.I
  have hzRe : z.re = -a := by simp [z, Complex.mul_re]
  have hzIm : z.im = ω := by simp [z, Complex.mul_im]
  have hz : z.re < 0 := by rw [hzRe]; exact neg_lt_zero.mpr ha
  have hexp := integrableOn_exp_mul_complex_Ioi hz 0
  have hre (s : ℝ) : (Complex.exp (z * (s : ℂ))).re =
      Real.exp (-a * s) * Real.cos (ω * s) := by
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, hzRe, hzIm]
  refine ⟨?_, ?_⟩
  · simpa only [RCLike.re_to_complex, hre] using hexp.re
  · calc
      _ = ∫ s : ℝ in Ioi 0, (Complex.exp (z * (s : ℂ))).re := by simp only [hre]
      _ = (∫ s : ℝ in Ioi 0, Complex.exp (z * (s : ℂ))).re := integral_re hexp
      _ = (-(z⁻¹)).re := by
        rw [integral_exp_mul_complex_Ioi hz 0]
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div, one_div]
      _ = _ := by
        simp only [Complex.neg_re, Complex.inv_re, Complex.normSq_apply, hzRe, hzIm,
          neg_mul_neg, pow_two, neg_div, neg_neg]

private theorem laplace_one_sub_cos {a : ℝ} (ha : 0 < a) (ω : ℝ) :
    IntegrableOn (fun s : ℝ => a * (Real.exp (-a * s) * (1 - Real.cos (ω * s)))) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, a * (Real.exp (-a * s) * (1 - Real.cos (ω * s)))) =
        ω ^ 2 / (a ^ 2 + ω ^ 2) := by
  have ha' : -a < 0 := neg_lt_zero.mpr ha
  have hexp := integrableOn_exp_mul_Ioi ha' 0
  obtain ⟨hcos, hcosIntegral⟩ := laplace_cos ha ω
  have hsplit : (fun s : ℝ => a * (Real.exp (-a * s) * (1 - Real.cos (ω * s)))) =
      fun s : ℝ => a * (Real.exp (-a * s) - Real.exp (-a * s) * Real.cos (ω * s)) := by
    funext s
    rw [mul_sub, mul_one]
  rw [hsplit]
  refine ⟨(hexp.sub hcos).const_mul a, ?_⟩
  rw [integral_const_mul, integral_sub hexp hcos, integral_exp_mul_Ioi ha' 0, hcosIntegral]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]
  have hden : a ^ 2 + ω ^ 2 ≠ 0 := by positivity
  field_simp [ha.ne', hden] <;> ring

theorem integrableOn_lowerTerm (ω : ℝ) (k : ℕ) : IntegrableOn (lowerTerm ω k) (Ioi 0) :=
  (laplace_one_sub_cos (decayRate_pos k) ω).1

/-- The integral of the `k + 1` exponential term after multiplication by `1 - cos (ωs)`. -/
theorem integral_lowerTerm (ω : ℝ) (k : ℕ) :
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
theorem integral_Ioi_lowerMode_eq_tsum (ω : ℝ) :
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
theorem integrableOn_lowerMode (ω : ℝ) : IntegrableOn (lowerMode ω) (Ioi 0) := by
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

-- Temporary copy of the private lemma in
-- D5/S3/Analytic/CothBernoulliDegree/PartialFraction.lean.
private lemma coth_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun k : ℕ => 2 / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2))
      (Real.cosh t / Real.sinh t / t - t ^ (-2 : ℤ)) := by
  let z : ℂ := (t : ℂ) * Complex.I / Real.pi
  have hz : z ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have hi := congrArg Complex.im hn
    simp [z, Complex.div_ofReal_im] at hi
    have : t / Real.pi > 0 := div_pos ht Real.pi_pos
    linarith
  have h := (summable_cotTerm hz).hasSum
  have he := cot_series_rep' hz
  have hs := h.congr_fun (fun k => (cotTerm_identity hz k).symm)
  rw [← he] at hs
  have hc : (Real.pi : ℂ) * Complex.cot (Real.pi * z) - 1 / z =
      ((Real.cosh t / Real.sinh t / t - t ^ (-2 : ℤ) : ℝ) : ℂ) *
        (-((Real.pi : ℂ) * (t : ℂ) * Complex.I)) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hsh : (Real.sinh t : ℂ) ≠ 0 := by exact_mod_cast (Real.sinh_pos_iff.mpr ht).ne'
    have hpiz : (Real.pi : ℂ) * z = (t : ℂ) * Complex.I := by dsimp [z]; field_simp
    rw [hpiz, Complex.cot_eq_cos_div_sin, Complex.cos_mul_I, Complex.sin_mul_I,
      ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    push_cast
    simp only [zpow_neg, zpow_ofNat]
    dsimp [z]
    field_simp
    simp [Complex.I_sq]
    <;> ring
  have hd : -((Real.pi : ℂ) * (t : ℂ) * Complex.I) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast ht.ne')) Complex.I_ne_zero)
  have hf (k : ℕ) :
      2 * z * (1 / ((z + (k + 1)) * (z - (k + 1)))) /
          (-((Real.pi : ℂ) * (t : ℂ) * Complex.I)) =
        ((2 / (t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2) : ℝ) : ℂ) := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
    have hden : (t : ℂ) ^ 2 + ((Real.pi : ℂ) * ((k : ℂ) + 1)) ^ 2 ≠ 0 := by
      exact_mod_cast (show t ^ 2 + (Real.pi * ((k : ℝ) + 1)) ^ 2 ≠ 0 by positivity)
    have hprod : (z + (k + 1)) * (z - (k + 1)) =
        -((t : ℂ) ^ 2 + ((Real.pi : ℂ) * ((k : ℂ) + 1)) ^ 2) / (Real.pi : ℂ) ^ 2 := by
      dsimp [z]
      field_simp
      <;> ring_nf
      <;> simp [Complex.I_sq]
    rw [hprod]
    push_cast
    dsimp [z]
    field_simp
    <;> ring
  have hres := (hs.div_const (-((Real.pi : ℂ) * (t : ℂ) * Complex.I))).congr_fun (fun k => (hf k).symm)
  rw [hc, mul_div_cancel_right₀ _ hd] at hres
  simpa only [Complex.ofReal_re] using Complex.hasSum_re hres

private theorem integral_Ioi_lowerMode_of_pos {ω : ℝ} (hω : 0 < ω) :
    (∫ s in Ioi 0, lowerMode ω s) =
      ((ω / 2) * (Real.cosh (ω / 2) / Real.sinh (ω / 2)) - 1) / 2 := by
  let x : ℝ := ω / 2
  have hx : 0 < x := div_pos hω (by norm_num)
  have hωx : ω = 2 * x := by dsimp [x]; ring
  have h := (coth_hasSum hx).mul_left (x ^ 2 / 2)
  have hs : HasSum (fun k : ℕ => ω ^ 2 / (decayRate k ^ 2 + ω ^ 2))
      (x ^ 2 / 2 * (Real.cosh x / Real.sinh x / x - x ^ (-2 : ℤ))) := by
    refine h.congr_fun fun k => ?_
    let b : ℝ := Real.pi * ((k : ℝ) + 1)
    have hb : 0 < b := by dsimp [b]; positivity
    have hrate : decayRate k = 2 * b := by
      dsimp [decayRate, b]
      ring
    have hden : x ^ 2 + b ^ 2 ≠ 0 := by positivity
    change ω ^ 2 / (decayRate k ^ 2 + ω ^ 2) = x ^ 2 / 2 * (2 / (x ^ 2 + b ^ 2))
    rw [hrate, hωx, show (2 * b) ^ 2 + (2 * x) ^ 2 = 4 * (x ^ 2 + b ^ 2) by ring]
    field_simp [hden] <;> ring
  have hvalue : x ^ 2 / 2 * (Real.cosh x / Real.sinh x / x - x ^ (-2 : ℤ)) =
      (x * (Real.cosh x / Real.sinh x) - 1) / 2 := by
    have hsh : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
    simp only [zpow_neg, zpow_ofNat]
    field_simp [hx.ne', hsh] <;> ring
  rw [integral_Ioi_lowerMode_eq_tsum, hs.tsum_eq, hvalue]

private theorem lowerMode_neg_frequency (ω s : ℝ) : lowerMode (-ω) s = lowerMode ω s := by
  simp only [lowerMode, neg_mul, Real.cos_neg]

/-- The positive-ray integral is half the coth expression at any nonzero frequency. -/
theorem integral_Ioi_lowerMode_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) :
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
/-- The compensated lower weight is integrable on the full real line. -/
theorem integrable_lowerMode (ω : ℝ) : Integrable (lowerMode ω) := by
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

theorem integral_lowerMode_eq_two_mul_Ioi (ω : ℝ) :
    (∫ s, lowerMode ω s) = 2 * ∫ s in Ioi 0, lowerMode ω s := by
  simpa only [lowerMode_abs] using (integral_comp_abs (f := lowerMode ω))

/-- The reflected series, with the positive integer `k + 1` in each denominator. -/
theorem integral_lowerMode_eq_tsum (ω : ℝ) :
    (∫ s, lowerMode ω s) = ∑' k : ℕ, 2 * ω ^ 2 / (decayRate k ^ 2 + ω ^ 2) := by
  rw [integral_lowerMode_eq_two_mul_Ioi, integral_Ioi_lowerMode_eq_tsum, ← tsum_mul_left]
  simp only [div_eq_mul_inv, mul_assoc]

/-- The full lower-boundary mode integral at a nonzero real frequency. -/
theorem integral_lowerMode_of_ne_zero {ω : ℝ} (hω : ω ≠ 0) :
    (∫ s, lowerMode ω s) = (ω / 2) * (Real.cosh (ω / 2) / Real.sinh (ω / 2)) - 1 := by
  rw [integral_lowerMode_eq_two_mul_Ioi, integral_Ioi_lowerMode_of_ne_zero hω]
  ring

@[simp] theorem lowerMode_zero (s : ℝ) : lowerMode 0 s = 0 := by
  simp [lowerMode]

@[simp] theorem integral_Ioi_lowerMode_zero : (∫ s in Ioi 0, lowerMode 0 s) = 0 := by
  simp

@[simp] theorem integral_lowerMode_zero : (∫ s, lowerMode 0 s) = 0 := by
  simp

/-- The whole-line coth formula with the zero-frequency branch. -/
theorem integral_lowerMode (ω : ℝ) :
    (∫ s, lowerMode ω s) =
      if ω = 0 then 0 else (ω / 2) * (Real.cosh (ω / 2) / Real.sinh (ω / 2)) - 1 := by
  by_cases hω : ω = 0
  · subst ω
    rw [ite_eq_left (rfl : (0 : ℝ) = 0)]
    exact integral_lowerMode_zero
  · rw [if_neg hω]
    exact integral_lowerMode_of_ne_zero hω

end

end PetzCothStripMode
