/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceEvaluation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite Vandermonde evaluation of the literal signed Gaussian source pairings. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceMeans

/-! Absolute regrouping ties the finite convolution to the original complex source pairing. -/

noncomputable section
open scoped BigOperators Topology ENNReal
open Filter

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation

open OriginalGaussianMatrix OriginalGaussianResolvent OriginalGaussianAllIndexResolvent
open OriginalGaussianExternalResolvent OriginalGaussianSourceMeans
open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open D5.S3.Analytic.OriginalHalfBinomialPeriod

private lemma weight_norm (n : ℕ) : ‖(centralWeight n : ℂ)‖ ≤ 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (centralWeight_nonneg n)]
    using weight_le_one n

private lemma signed_weight (n : ℕ) :
    (centralWeight n : ℂ) = (-1 : ℂ) ^ n * Ring.choose (-1 / 2 : ℂ) n := by
  rw [← halfBinomial_choose, halfBinomial_eq_signed_centralWeight, ← mul_assoc,
    ← pow_add, ← two_mul n, pow_mul]
  norm_num

private lemma finite_convolution (a : ℂ) (n : ℕ) :
    (∑ s ∈ Finset.range (n + 1), (-1 : ℂ) ^ s * Ring.choose a s *
      (centralWeight (n - s) : ℂ)) =
        (-1 : ℂ) ^ n * Ring.choose (a - 1 / 2) n := by
  rw [show a - 1 / 2 = a + (-1 / 2) by ring,
    Ring.add_choose_eq n (Commute.all _ _),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hn : s + (n - s) = n := by have := Finset.mem_range.mp hs; omega
  rw [signed_weight]
  have hp : (-1 : ℂ) ^ n = (-1 : ℂ) ^ s * (-1 : ℂ) ^ (n - s) := by
    rw [← pow_add, hn]
  rw [hp]
  ring

lemma external_parameter_bound (out : Bool) (p : ℕ) :
    ‖(if out then (p : ℂ) + 1 / 2 else -(p : ℂ) - 1 / 2)‖ ≤ (p + 1 : ℝ) := by
  cases out
  · rw [ite_eq_right (by decide), show -(p : ℂ) - 1 / 2 = ((-p - 1 / 2 : ℝ) : ℂ) by
      push_cast; rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by have := Nat.cast_nonneg (α := ℝ) p; linarith)]
    linarith
  · rw [ite_eq_left rfl, show (p : ℂ) + 1 / 2 = ((p + 1 / 2 : ℝ) : ℂ) by
      push_cast; rfl, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith

private def convolutionTerm (out : Bool) (p : ℕ) (x : ℂ) (sk : ℕ × ℕ) : ℂ :=
  (-1 : ℂ) ^ sk.1 * externalBinomial out p sk.1 *
    (centralWeight sk.2 : ℂ) * centralWeight (sk.2 + sk.1) * x ^ (sk.1 + sk.2)

private lemma convolution_summable (out : Bool) (p : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (fun sk : ℕ × ℕ => ‖convolutionTerm out p x sk‖) := by
  have hb := summable_choose_mul_geometric_of_norm_lt_one p
    (r := ‖x‖) (by simpa using hx)
  have hg := summable_geometric_of_lt_one (norm_nonneg x) hx
  have h := hb.mul_of_nonneg hg (fun s => by positivity) (fun k => by positivity)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun sk => ?_) h
  simp only [convolutionTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    pow_add]
  have hc : ‖externalBinomial out p sk.1‖ ≤ ((p + sk.1).choose sk.1 : ℝ) :=
    choose_bound p (external_parameter_bound out p) sk.1
  calc
    _ ≤ ((p + sk.1).choose sk.1 : ℝ) * 1 * 1 * (‖x‖ ^ sk.1 * ‖x‖ ^ sk.2) := by
      gcongr
      · exact weight_norm _
      · exact weight_norm _
    _ = _ := by rw [Nat.add_comm p sk.1, Nat.choose_symm_add]; ring

private lemma convolution_row (out : Bool) (p : ℕ) (x : ℂ) (s : ℕ) :
    (∑' k : ℕ, convolutionTerm out p x (s, k)) =
      (-1 : ℂ) ^ s * externalBinomial out p s * x ^ s * shiftedCentralSeries x s := by
  rw [shiftedCentralSeries, ← tsum_mul_left]
  exact tsum_congr (fun k => by simp only [convolutionTerm, pow_add]; ring)

/-- The evaluated diagonal column includes the internal zero frequency. -/
def sourceAmplitude (out : Bool) (p : ℕ) (x : ℂ) : ℂ :=
  ∑' n : ℕ, (centralWeight n : ℂ) * (-1 : ℂ) ^ n *
    Ring.choose ((if out then (p : ℂ) + 1 / 2 else -(p : ℂ) - 1 / 2) - 1 / 2) n * x ^ n

private lemma diagonal_evaluation (out : Bool) (p : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    (∑' s : ℕ, (-1 : ℂ) ^ s * externalBinomial out p s * x ^ s *
      shiftedCentralSeries x s) = sourceAmplitude out p x := by
  have hs := (convolution_summable out p hx).of_norm
  rw [← tsum_congr (convolution_row out p x), ← hs.tsum_prod]
  change (∑' sk : ℕ × ℕ, convolutionTerm out p x sk) = _
  have hregroup : (∑' sk : ℕ × ℕ, convolutionTerm out p x sk) =
      ∑' n : ℕ, ∑ sk ∈ Finset.HasAntidiagonal.antidiagonal n,
        convolutionTerm out p x sk := by
    conv_rhs =>
      congr
      ext n
      rw [← Finset.sum_finset_coe, ← tsum_fintype (L := .unconditional _)]
    rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq
      (convolutionTerm out p x)]
    exact (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hs).tsum_sigma'
      (fun n => (hasSum_fintype _).summable)
  rw [hregroup, sourceAmplitude]
  apply tsum_congr
  intro n
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  calc
    _ = (centralWeight n : ℂ) *
        (∑ s ∈ Finset.range (n + 1), (-1 : ℂ) ^ s * externalBinomial out p s *
          (centralWeight (n - s) : ℂ)) * x ^ n := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro s hs
      have hn : s + (n - s) = n := by have := Finset.mem_range.mp hs; omega
      simp only [convolutionTerm, hn, Nat.sub_add_cancel (Nat.le_of_lt_succ (Finset.mem_range.mp hs))]
      ring
    _ = _ := by simp_rw [externalBinomial]; rw [finite_convolution]; ring

/-- The full diagonal convolution is normally summable for every signed external mode. -/
theorem sourceAmplitude_hasSum (out : Bool) (p : ℕ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun s : ℕ => (-1 : ℂ) ^ s * externalBinomial out p s * x ^ s *
      shiftedCentralSeries x s) (sourceAmplitude out p x) := by
  have hs := ((convolution_summable out p hx).of_norm.prod).congr
    (convolution_row out p x)
  rw [← diagonal_evaluation out p hx]
  exact hs.hasSum

/-- The sign is fixed by the actual source pairing, for both signed labels and every mode. -/
theorem sourceExternal_evaluation (out : Bool) (p : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    1 - sourceExternal out p z = sourceAmplitude out p (z ^ 2) / period (z ^ 2) := by
  have hx : ‖z ^ 2‖ < 1 := by
    rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num)
  have hs := ((convolution_summable out p hx).of_norm.prod).congr
    (convolution_row out p (z ^ 2))
  have he := diagonal_evaluation out p hx
  rw [hs.tsum_eq_zero_add] at he
  have hzero : shiftedCentralSeries (z ^ 2) 0 = period (z ^ 2) := by
    rw [shiftedCentralSeries, period]
    apply tsum_congr
    intro k
    rw [halfBinomial_eq_signed_centralWeight]
    simp only [Nat.add_zero, mul_pow]
    have hp : ((-1 : ℂ) ^ k) ^ 2 = 1 := by
      rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
      norm_num
    rw [hp]
    ring
  have hb0 : externalBinomial out p 0 = 1 := by simp [externalBinomial]
  simp only [pow_zero, hb0, one_mul, mul_one, hzero] at he
  rw [sourceExternal, tsum_div_const]
  have he' : (∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * externalBinomial out p (n + 1) *
      z ^ (2 * (n + 1)) * shiftedCentralSeries (z ^ 2) (n + 1)) =
      sourceAmplitude out p (z ^ 2) - period (z ^ 2) := by
    rw [← he]
    simp only [add_sub_cancel_left]
    exact tsum_congr (fun n => by rw [pow_mul] <;> ring)
  rw [he']
  field_simp [OriginalGaussianPeriodIdentity.period_ne_zero hx]
  ring

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSourceEvaluation
