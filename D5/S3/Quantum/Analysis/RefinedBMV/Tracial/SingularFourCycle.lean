/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/SingularFourCycle
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Opposite endpoint compensation for a four-cycle with a zero spectral node. -/

import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.OneZeroMatching
import D5.S3.Quantum.Analysis.RefinedBMV.Tracial.BetaBinomialHarmonic
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation

namespace RefinedBMV.Tracial

open FourCopyGap Filter Set Topology
open private balanced monomial
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.FourCopyGap
open private gapDefect_zero completeThree_eq_sum completeTwo_diag
  from D5.S3.Quantum.Analysis.RefinedBMV.Tracial.OneZeroMatching
open private gapDefect_scale
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumAllocation
open private RefinedBMV.ThreeBlockGram.ZeroSpectrum.card_gaps_real
  from D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumCounts

private theorem gapDefect_repeated_eq_moment (p : ℕ) (hp : 0 < p) {a b : ℝ} (ha : 0 < a) :
    gapDefect p b a 0 a =
      a ^ p * ∑ k ∈ Finset.range (p + 1), (((p - k : ℕ) : ℝ) + 1) * (b / a) ^ k := by
  rw [gapDefect_zero p hp, completeThree_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hpow : a ^ p = a ^ k * a ^ (p - k) := by
    have hk' := Finset.mem_range.mp hk
    rw [← pow_add, show k + (p - k) = p by omega]
  rw [completeTwo_diag, div_pow, hpow]
  field_simp [ha.ne']

private theorem moment_product_le (p : ℕ) (hp : 2 ≤ p) {a c b : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hb : 0 < b) (hac : a * c = 1) :
    ((gaps p).card * b ^ ((p : ℝ) / 2)) ^ 2 ≤
      4 * (gapDefect p b a 0 a * gapDefect p b c 0 c) * oneZeroMomentPolynomial p (b / a) := by
  have h := one_zero_polynomial_moment_product p hp (Real.log a) (Real.log b)
  dsimp only at h
  have h₁ : Real.exp (Real.log b - Real.log a) = b / a := by
    rw [Real.exp_sub, Real.exp_log hb, Real.exp_log ha]
  have h₂ : Real.exp (Real.log b + Real.log a) = b / c := by
    rw [Real.exp_add, Real.exp_log hb, Real.exp_log ha]
    exact (eq_div_iff hc.ne').mpr (by linear_combination b * hac)
  have h₃ : Real.exp ((p : ℝ) * Real.log b) = b ^ p := by
    rw [Real.exp_nat_mul, Real.exp_log hb]
  simp only [h₁, h₂, h₃] at h
  have hXY : gapDefect p b a 0 a * gapDefect p b c 0 c =
      (∑ k ∈ Finset.range (p + 1), (((p - k : ℕ) : ℝ) + 1) * (b / a) ^ k) *
      (∑ k ∈ Finset.range (p + 1), (((p - k : ℕ) : ℝ) + 1) * (b / c) ^ k) := by
    rw [gapDefect_repeated_eq_moment p (by omega) ha, gapDefect_repeated_eq_moment p (by omega) hc]
    have hscale : a ^ p * c ^ p = 1 := by rw [← mul_pow, hac, one_pow]
    linear_combination
      (∑ k ∈ Finset.range (p + 1), (((p - k : ℕ) : ℝ) + 1) * (b / a) ^ k) *
      (∑ k ∈ Finset.range (p + 1), (((p - k : ℕ) : ℝ) + 1) * (b / c) ^ k) * hscale
  have hQ : ((gaps p).card * b ^ ((p : ℝ) / 2)) ^ 2 =
      (((p : ℝ) + 1) * ((p : ℝ) + 2) * ((p : ℝ) + 3) / 6) ^ 2 * b ^ p := by
    rw [mul_pow, ← Real.rpow_mul_natCast hb.le]
    rw [show (p : ℝ) / 2 * ((2 : ℕ) : ℝ) = p by norm_num, Real.rpow_natCast,
      RefinedBMV.ThreeBlockGram.ZeroSpectrum.card_gaps_real]
    unfold RefinedBMV.ThreeBlockGram.ZeroSpectrum.N RefinedBMV.ThreeBlockGram.ZeroSpectrum.q
    ring
  rw [hXY, hQ]
  simpa only [oneZeroMomentPolynomial] using h

/-- The four-label scalar gap is paid by its two opposite endpoint matchings
when one label vanishes. This form uses positive, distinct remaining labels
after normalization by the geometric mean of an opposite pair. -/
theorem gapDefect_one_zero_normalized_of_two_le (p : ℕ) (hp : 2 ≤ p) {a c b : ℝ}
    (ha : 1 ≤ a) (hc : 0 < c) (hb : 0 < b) (hac : a * c = 1)
    (hab : a ≠ b) (hcb : c ≠ b) (hneq : a ≠ c) :
    gapDefect p b c 0 a ≤ Real.sqrt (gapDefect p b a 0 a * gapDefect p b c 0 c) +
      Real.sqrt (gapDefect p b b c a * gapDefect p 0 c 0 a) :=
  gapDefect_one_zero_le_of_moment_product_le p (by omega) ha hb hac hab hcb hneq
    (moment_product_le p hp (by positivity) hc hb hac)


private theorem gapDefect_one_zero_normalized (p : ℕ) (hp : 0 < p) {a c b : ℝ}
    (ha : 1 ≤ a) (hc : 0 < c) (hb : 0 < b) (hac : a * c = 1)
    (hab : a ≠ b) (hcb : c ≠ b) (hneq : a ≠ c) :
    gapDefect p b c 0 a ≤ Real.sqrt (gapDefect p b a 0 a * gapDefect p b c 0 c) +
      Real.sqrt (gapDefect p b b c a * gapDefect p 0 c 0 a) := by
  by_cases hp' : 2 ≤ p
  · exact gapDefect_one_zero_normalized_of_two_le p hp' ha hc hb hac hab hcb hneq
  · have he : p = 1 := by omega
    rw [he]
    exact gapDefect_one_zero_le_at_one (by positivity) hc hb hac hab hcb hneq

private theorem gapDefect_one_zero_ordered_distinct (p : ℕ) (hp : 0 < p) {a c b : ℝ}
    (hc : 0 < c) (hb : 0 < b) (hca : c < a) (hab : a ≠ b) (hcb : c ≠ b) :
    gapDefect p b c 0 a ≤ Real.sqrt (gapDefect p b a 0 a * gapDefect p b c 0 c) +
      Real.sqrt (gapDefect p b b c a * gapDefect p 0 c 0 a) := by
  have ha : 0 < a := hc.trans hca
  let r := Real.sqrt (a * c)
  let t := r⁻¹
  have hr : 0 < r := Real.sqrt_pos_of_pos (mul_pos ha hc)
  have ht : 0 < t := inv_pos.mpr hr
  have hsq : r ^ 2 = a * c := Real.sq_sqrt (mul_nonneg ha.le hc.le)
  have hac : (t * a) * (t * c) = 1 := by
    calc
      (t * a) * (t * c) = (r ^ 2)⁻¹ * (a * c) := by dsimp only [t]; ring
      _ = 1 := by rw [hsq, inv_mul_cancel₀ (mul_pos ha hc).ne']
  have htl : 1 ≤ t * a := by
    have h : r ≤ a := Real.sqrt_le_iff.mpr ⟨ha.le, by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hca.le ha.le⟩
    calc
      1 = t * r := (inv_mul_cancel₀ hr.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h ht.le
  have h := gapDefect_one_zero_normalized p hp htl (mul_pos ht hc) (mul_pos ht hb) hac
    (fun e ↦ hab (mul_left_cancel₀ ht.ne' e)) (fun e ↦ hcb (mul_left_cancel₀ ht.ne' e))
    (fun e ↦ hca.ne' (mul_left_cancel₀ ht.ne' e))
  have hScale {u v w z : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hz : 0 ≤ z) :
      gapDefect p (t * u) (t * v) (t * w) (t * z) = t ^ p * gapDefect p u v w z :=
    gapDefect_scale p ht.le hu hv hw hz
  have hsqrt (u v : ℝ) : Real.sqrt ((t ^ p * u) * (t ^ p * v)) =
      t ^ p * Real.sqrt (u * v) := by
    rw [show (t ^ p * u) * (t ^ p * v) = (t ^ p) ^ 2 * (u * v) by ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg ht.le p)]
  rw [← mul_zero t] at h
  rw [hScale hb.le hc.le le_rfl ha.le, hScale hb.le ha.le le_rfl ha.le,
    hScale hb.le hc.le le_rfl hc.le, hScale hb.le hb.le hc.le ha.le,
    hScale le_rfl hc.le le_rfl ha.le, hsqrt, hsqrt, ← mul_add] at h
  exact (mul_le_mul_iff_of_pos_left (pow_pos ht p)).mp h


private theorem continuous_gapDefect_fun (p : ℕ) {u v w z : ℝ → ℝ}
    (hu : Continuous u) (hv : Continuous v) (hw : Continuous w) (hz : Continuous z) :
    Continuous (fun x ↦ gapDefect p (u x) (v x) (w x) (z x)) := by
  have hr : Continuous (fun y : ℝ ↦ y ^ ((p : ℝ) / 4)) :=
    Real.continuous_rpow_const (by positivity)
  have h (f : ℝ → ℝ) (hf : Continuous f) :
      Continuous (fun x ↦ f x ^ ((p : ℝ) / 4)) := hr.comp hf
  unfold gapDefect balanced
  refine (continuous_finsetSum _ fun g _ ↦ ?_).sub
    (continuous_const.mul (((h u hu).mul (h v hv)).mul (h w hw) |>.mul (h z hz)))
  unfold monomial
  fun_prop

private theorem eventually_affine_ne {a b d e : ℝ} (hde : d ≠ e) :
    ∀ᶠ t in 𝓝[Set.Ioi (0 : ℝ)] 0, a + d * t ≠ b + e * t := by
  by_cases hab : a = b
  · filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    intro he
    exact hde (mul_right_cancel₀ ht'.ne' (by linarith only [he, hab]))
  · have h : ContinuousAt (fun t : ℝ ↦ (a + d * t) - (b + e * t)) 0 := by fun_prop
    have h₀ : ((a + d * (0 : ℝ)) - (b + e * 0)) ≠ 0 := by
      simpa only [mul_zero, add_zero, sub_ne_zero] using hab
    exact ((h.eventually_ne h₀).filter_mono nhdsWithin_le_nhds).mono
      fun _ ht ↦ sub_ne_zero.mp ht

private theorem gapDefect_one_zero_ordered (p : ℕ) (hp : 0 < p) {a c b : ℝ}
    (hc : 0 ≤ c) (hb : 0 ≤ b) (hca : c ≤ a) :
    gapDefect p b c 0 a ≤ Real.sqrt (gapDefect p b a 0 a * gapDefect p b c 0 c) +
      Real.sqrt (gapDefect p b b c a * gapDefect p 0 c 0 a) := by
  let A (t : ℝ) := a + 3 * t
  let C (t : ℝ) := c + t
  let B (t : ℝ) := b + 2 * t
  have hA : Continuous A := by unfold A; fun_prop
  have hC : Continuous C := by unfold C; fun_prop
  have hB : Continuous B := by unfold B; fun_prop
  have hzero : Continuous (fun _ : ℝ ↦ (0 : ℝ)) := continuous_const
  have hlc := continuous_gapDefect_fun p hB hC hzero hA
  have hrc := ((Real.continuous_sqrt.comp
    ((continuous_gapDefect_fun p hB hA hzero hA).mul
      (continuous_gapDefect_fun p hB hC hzero hC))).add
    (Real.continuous_sqrt.comp
      ((continuous_gapDefect_fun p hB hB hC hA).mul
        (continuous_gapDefect_fun p hzero hC hzero hA))))
  have hl := hlc.continuousAt (x := 0) |>.continuousWithinAt (s := Set.Ioi (0 : ℝ))
  have hr := hrc.continuousAt (x := 0) |>.continuousWithinAt (s := Set.Ioi (0 : ℝ))
  have h := le_of_tendsto_of_tendsto hl hr (by
    filter_upwards [self_mem_nhdsWithin,
        eventually_affine_ne (a := a) (b := b) (d := 3) (e := 2) (by norm_num),
        eventually_affine_ne (a := c) (b := b) (d := 1) (e := 2) (by norm_num)]
        with t ht hab hcb
    have ht' : 0 < t := ht
    have hc' : 0 < C t := by unfold C; linarith only [hc, ht']
    have hb' : 0 < B t := by unfold B; linarith only [hb, ht']
    have hca' : C t < A t := by unfold C A; linarith only [hca, ht']
    exact gapDefect_one_zero_ordered_distinct p hp hc' hb' hca' hab (by simpa [C, B] using hcb))
  simpa [A, B, C] using h

private theorem gapDefect_swap_opposite (p : ℕ) (a b c d : ℝ) :
    gapDefect p a b c d = gapDefect p a d c b := by
  rw [ThreeBlockGram.gapDefect_swap23 p a b c d, ThreeBlockGram.gapDefect_swap12 p a b d c,
    ThreeBlockGram.gapDefect_swap23 p a d b c]

/-- All integer first degrees satisfy the four-cycle two-matching inequality
when at least one label is zero. Repeated and zero remaining labels are allowed. -/
theorem gapDefect_one_zero_le (p : ℕ) (hp : 0 < p) {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    gapDefect p b c 0 a ≤ Real.sqrt (gapDefect p b a 0 a * gapDefect p b c 0 c) +
      Real.sqrt (gapDefect p b b c a * gapDefect p 0 c 0 a) := by
  rcases le_total c a with h | h
  · exact gapDefect_one_zero_ordered p hp hc hb h
  · have he := gapDefect_one_zero_ordered p hp ha hb h
    rw [gapDefect_swap_opposite p b a 0 c, gapDefect_swap_opposite p 0 a 0 c,
      ThreeBlockGram.gapDefect_swap23 p b b a c,
      mul_comm (gapDefect p b c 0 c) (gapDefect p b a 0 a)] at he
    exact he

#print axioms gapDefect_one_zero_normalized_of_two_le
#print axioms gapDefect_one_zero_le

end RefinedBMV.Tracial
