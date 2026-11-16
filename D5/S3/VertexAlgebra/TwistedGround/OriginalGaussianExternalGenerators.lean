/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Normally convergent signed mode generators of the literal source amplitudes. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalNormal
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalSourceJet
import Mathlib.Analysis.Analytic.Binomial

/-! The mode sums are identified by reindexing the finite binomial convolution. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology ENNReal
namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianAllIndexResolvent
open OriginalGaussianSourceEvaluation OriginalGaussianExternalNormal
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection

def centralGenerating (t : ℂ) : ℂ := ∑' n : ℕ, (centralWeight n : ℂ) * t ^ n

private lemma centralGenerating_evaluation {t : ℂ} (ht : ‖t‖ < 1) :
    centralGenerating t = (1 - t) ^ (-1 / 2 : ℂ) := by
  have hm : -t ∈ Metric.eball (0 : ℂ) (1 : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using ht
  have h := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := (-1 / 2 : ℂ))).hasSum hm
  simp only [← sub_eq_add_neg, binomialSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul] at h
  have he (n : ℕ) : Ring.choose (-1 / 2 : ℂ) n * (-t) ^ n =
      (centralWeight n : ℂ) * t ^ n := by
    rw [← halfBinomial_choose, halfBinomial_eq_signed_centralWeight, neg_pow]
    have hn : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
      rw [← pow_add, ← two_mul n, pow_mul]
      norm_num
    calc
      _ = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * (centralWeight n : ℂ) * t ^ n := by ring
      _ = _ := by rw [hn, one_mul]
  simpa only [centralGenerating, sub_eq_add_neg, zero_add] using
    (h.congr_fun (fun n => (he n).symm)).tsum_eq

def amplitudeTerm (out : Bool) (u x : ℂ) (pn : ℕ × ℕ) : ℂ :=
  (centralWeight pn.2 : ℂ) * (-1 : ℂ) ^ pn.2 *
    Ring.choose ((if out then (pn.1 : ℂ) + 1 / 2 else -(pn.1 : ℂ) - 1 / 2) -
      1 / 2) pn.2 * x ^ pn.2 * u ^ pn.1

private lemma amplitudeTerm_positive (u x : ℂ) (p n : ℕ) :
    amplitudeTerm true u x (p, n) =
      (centralWeight n : ℂ) * (-1 : ℂ) ^ n * (p.choose n : ℂ) * x ^ n * u ^ p := by
  simp [amplitudeTerm, Ring.choose_natCast]

private lemma amplitudeTerm_negative (u x : ℂ) (p n : ℕ) :
    amplitudeTerm false u x (p, n) =
      (centralWeight n : ℂ) * ((p + n).choose n : ℂ) * x ^ n * u ^ p := by
  have he : (-(p : ℂ) - 1 / 2) - 1 / 2 = -((p : ℂ) + 1) := by ring
  rw [amplitudeTerm, ite_eq_right (by decide), he, Ring.choose_neg]
  simp only [show (p : ℂ) + 1 + n - 1 = ((p + n : ℕ) : ℂ) by push_cast; ring,
    Ring.choose_natCast, Units.smul_def, zsmul_eq_mul, Int.cast_negOnePow_natCast]
  have hn : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← pow_add, ← two_mul n, pow_mul]
    norm_num
  calc
    _ = ((centralWeight n : ℂ) * ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n)) *
      ((p + n).choose n : ℂ) * x ^ n * u ^ p := by ring
    _ = _ := by rw [hn, mul_one]

private lemma choose_power_hasSum (n : ℕ) {u : ℂ} (hu : ‖u‖ < 1) :
    HasSum (fun p : ℕ => (p.choose n : ℂ) * u ^ p)
      (u ^ n / (1 - u) ^ (n + 1)) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one n hu).mul_left (u ^ n)
  have hz : (∑ p ∈ Finset.range n, (p.choose n : ℂ) * u ^ p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    simp [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hp)]
  rw [← hasSum_nat_add_iff' n]
  simp only [hz, sub_zero]
  convert h using 1
  · ext p
    rw [pow_add]
    ring
  · ring

private lemma amplitudeTerm_row (out : Bool) (p : ℕ) (u x : ℂ) :
    (∑' n : ℕ, amplitudeTerm out u x (p, n)) = sourceAmplitude out p x * u ^ p := by
  rw [sourceAmplitude, ← tsum_mul_right]
  rfl

/-- Both signed mode series converge normally in the elementary joint disk. -/
theorem sourceAmplitude_mode_hasSum (out : Bool) {u x : ℂ}
    (hsmall : ‖u‖ + ‖x‖ < 1) :
    HasSum (fun p : ℕ => sourceAmplitude out p x * u ^ p)
      (∑' n : ℕ, ∑' p : ℕ, amplitudeTerm out u x (p, n)) := by
  have hs : Summable (amplitudeTerm out u x) :=
    (sourceAmplitude_joint_summable out hsmall).of_norm
  have hrow := hs.prod.congr (amplitudeTerm_row out · u x)
  have ht : (∑' p : ℕ, sourceAmplitude out p x * u ^ p) =
      ∑' n : ℕ, ∑' p : ℕ, amplitudeTerm out u x (p, n) := by
    rw [← tsum_congr (amplitudeTerm_row out · u x)]
    have hs' : Summable (Function.uncurry (fun p n : ℕ => amplitudeTerm out u x (p, n))) := hs
    exact hs'.tsum_comm.symm
  rw [← ht]
  exact hrow.hasSum

/-- Reindexing evaluates the positive signed mode generator. -/
theorem sourceAmplitude_positive_generator {u x : ℂ}
    (hsmall : ‖u‖ + ‖x‖ < 1) :
    HasSum (fun p : ℕ => sourceAmplitude true p x * u ^ p)
      ((1 / (1 - u)) * centralGenerating (-x * u / (1 - u))) := by
  have hu : ‖u‖ < 1 := by linarith [norm_nonneg x]
  have h := sourceAmplitude_mode_hasSum true hsmall
  convert h using 1
  symm
  rw [centralGenerating, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp_rw [amplitudeTerm_positive]
  have he (p : ℕ) : (centralWeight n : ℂ) * (-1 : ℂ) ^ n *
      (p.choose n : ℂ) * x ^ n * u ^ p =
      ((centralWeight n : ℂ) * (-1 : ℂ) ^ n * x ^ n) * ((p.choose n : ℂ) * u ^ p) := by
    ring
  simp_rw [he]
  rw [tsum_mul_left, (choose_power_hasSum n hu).tsum_eq]
  rw [div_pow, mul_pow, pow_succ, div_eq_mul_inv, mul_inv_rev, neg_pow]
  ring

/-- Reindexing evaluates the negative signed mode generator without an Euler transformation. -/
theorem sourceAmplitude_negative_generator {u x : ℂ}
    (hsmall : ‖u‖ + ‖x‖ < 1) :
    HasSum (fun p : ℕ => sourceAmplitude false p x * u ^ p)
      ((1 / (1 - u)) * centralGenerating (x / (1 - u))) := by
  have hu : ‖u‖ < 1 := by linarith [norm_nonneg x]
  have h := sourceAmplitude_mode_hasSum false hsmall
  convert h using 1
  symm
  rw [centralGenerating, ← tsum_mul_left]
  apply tsum_congr
  intro n
  simp_rw [amplitudeTerm_negative]
  have he (p : ℕ) : (centralWeight n : ℂ) * ((p + n).choose n : ℂ) * x ^ n * u ^ p =
      ((centralWeight n : ℂ) * x ^ n) * (((p + n).choose n : ℂ) * u ^ p) := by ring
  simp_rw [he]
  rw [tsum_mul_left, (hasSum_choose_mul_geometric_of_norm_lt_one n hu).tsum_eq,
    div_pow, pow_succ, div_eq_mul_inv, mul_inv_rev]
  ring

private lemma generator_arguments {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1) :
    ‖-x * u / (1 - u)‖ < 1 ∧ ‖x / (1 - u)‖ < 1 := by
  have hu : ‖u‖ < 1 := by linarith [norm_nonneg x]
  have hd : 1 - ‖u‖ ≤ ‖1 - u‖ := by
    simpa only [norm_one] using norm_sub_norm_le (1 : ℂ) u
  have hpos : 0 < ‖1 - u‖ := by linarith
  constructor
  · rw [norm_div, norm_mul, norm_neg]
    apply (div_lt_one hpos).mpr
    calc
      ‖x‖ * ‖u‖ ≤ ‖x‖ := mul_le_of_le_one_right (norm_nonneg x) hu.le
      _ < ‖1 - u‖ := by linarith
  · rw [norm_div]
    exact (div_lt_one hpos).mpr (by linarith)

/-- The signed generators are the analytic binomial branches, without singular chart values. -/
theorem sourceAmplitude_generators {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1) :
    HasSum (fun p : ℕ => sourceAmplitude true p x * u ^ p)
      ((1 / (1 - u)) * (1 + x * u / (1 - u)) ^ (-1 / 2 : ℂ)) ∧
    HasSum (fun p : ℕ => sourceAmplitude false p x * u ^ p)
      ((1 / (1 - u)) * (1 - x / (1 - u)) ^ (-1 / 2 : ℂ)) := by
  have hp := sourceAmplitude_positive_generator hsmall
  have hn := sourceAmplitude_negative_generator hsmall
  rw [centralGenerating_evaluation (generator_arguments hsmall).1] at hp
  rw [centralGenerating_evaluation (generator_arguments hsmall).2] at hn
  have he : 1 - -x * u / (1 - u) = 1 + x * u / (1 - u) := by ring
  rw [he] at hp
  exact ⟨hp, hn⟩

/-- The generator is defined from the actual amplitudes, before its closed evaluation. -/
def sourceMode (out : Bool) (u x : ℂ) : ℂ :=
  ∑' p : ℕ, sourceAmplitude out p x * u ^ p

private lemma sourceMode_explicit {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1) :
    sourceMode true u x =
      (1 / (1 - u)) * (1 + x * u / (1 - u)) ^ (-1 / 2 : ℂ) ∧
    sourceMode false u x =
      (1 / (1 - u)) * (1 - x / (1 - u)) ^ (-1 / 2 : ℂ) :=
  ⟨(sourceAmplitude_generators hsmall).1.tsum_eq,
    (sourceAmplitude_generators hsmall).2.tsum_eq⟩

/-- The actual generators have the required algebraic squares on their legitimate local disk. -/
theorem sourceMode_square {u x : ℂ} (hsmall : ‖u‖ + ‖x‖ < 1) :
    sourceMode true u x ^ 2 = 1 / ((1 - u) * (1 - (1 - x) * u)) ∧
    sourceMode false u x ^ 2 = 1 / ((1 - u) * (1 - x - u)) := by
  have hu : ‖u‖ < 1 := by linarith [norm_nonneg x]
  have hune : 1 - u ≠ 0 := sub_ne_zero.mpr (by
    intro he
    have := congrArg norm he
    simp only [norm_one] at this
    linarith)
  have hp (t : ℂ) : (t ^ (-1 / 2 : ℂ)) ^ 2 = 1 / t := by
    rw [← Complex.cpow_mul_nat]
    norm_num [Complex.cpow_neg_one]
  rw [(sourceMode_explicit hsmall).1, (sourceMode_explicit hsmall).2,
    mul_pow, mul_pow, hp, hp]
  constructor
  · field_simp [hune]
    ring
  · field_simp [hune]
    ring


end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGenerators
