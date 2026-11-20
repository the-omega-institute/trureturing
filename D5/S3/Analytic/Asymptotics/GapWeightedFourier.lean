/- GID: D5/S3/Analytic/Asymptotics/GapWeightedFourier
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/GapWeightedFourier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gap-weighted averages recover coefficients on a closed upper line. -/

import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Fourier recovery from samples on a mesh with vanishing gaps

Weight each left sample by the length of its mesh interval. Normalizing by
the covered length gives orthogonality of real frequencies in the limit.
Absolute summability permits recovery of the sum of all coefficients at a
specified frequency, with an additive sample error tending to zero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Asymptotics
open scoped BigOperators Topology

namespace GapWeightedFourier

/-- The length of the interval starting at the sample with index `k`. -/
def gap (y : ℕ → ℝ) (k : ℕ) : ℝ := y (k + 1) - y k

/-- The gap-weighted average of the first `M` samples. At `M = 0` it is zero. -/
def average (y : ℕ → ℝ) (a : ℕ → ℂ) (M : ℕ) : ℂ :=
  (∑ k ∈ Finset.range M, (gap y k : ℂ) * a k) / (↑(y M - y 0) : ℂ)

/-- The complex exponential of real frequency `μ` at `x`. -/
def phase (μ x : ℝ) : ℂ := Complex.exp (Complex.I * (μ : ℂ) * (x : ℂ))

private theorem norm_phase (μ x : ℝ) : ‖phase μ x‖ = 1 := by
  rw [phase, mul_assoc, ← Complex.ofReal_mul, Complex.norm_exp_I_mul_ofReal]

private theorem gap_nonneg {y : ℕ → ℝ} (hm : StrictMono y) (k : ℕ) : 0 ≤ gap y k :=
  sub_nonneg.mpr (hm (Nat.lt_succ_self k)).le

private theorem sum_gap (y : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.range M, gap y k) = y M - y 0 := by
  exact Finset.sum_range_sub y M

private theorem tendsto_span {y : ℕ → ℝ} (hy : Tendsto y atTop atTop) :
    Tendsto (fun M => y M - y 0) atTop atTop := by
  refine tendsto_atTop.2 fun t => ?_
  filter_upwards [hy.eventually (eventually_ge_atTop (t + y 0))] with M hM
  exact le_sub_iff_add_le.mpr hM

private theorem average_add (y : ℕ → ℝ) (a b : ℕ → ℂ) (M : ℕ) :
    average y (fun k => a k + b k) M = average y a M + average y b M := by
  simp only [average, mul_add, Finset.sum_add_distrib, add_div]

private theorem average_const {y : ℕ → ℝ} (hm : StrictMono y)
    {M : ℕ} (hM : 0 < M) (z : ℂ) : average y (fun _ => z) M = z := by
  have hd : (↑(y M - y 0) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (hm hM).ne')
  rw [average, ← Finset.sum_mul, ← Complex.ofReal_sum, sum_gap, mul_comm]
  exact mul_div_cancel_right₀ z hd

/-- A summand bounded by its gap times a null sequence contributes zero in
the limit. The finite-prefix estimate is `Asymptotics.IsLittleO.sum_range`. -/
private theorem tendsto_normalized_sum_zero {y : ℕ → ℝ} (hm : StrictMono y)
    (hy : Tendsto y atTop atTop) {f : ℕ → ℂ} {b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 0)) (hf : ∀ k, ‖f k‖ ≤ b k * gap y k) :
    Tendsto (fun M => (∑ k ∈ Finset.range M, f k) / (↑(y M - y 0) : ℂ)) atTop (𝓝 0) := by
  have hs : f =o[atTop] gap y := by
    refine isLittleO_iff.mpr fun ε hε => ?_
    filter_upwards [hb.eventually (gt_mem_nhds hε)] with k hk
    rw [Real.norm_of_nonneg (gap_nonneg hm k)]
    exact (hf k).trans (mul_le_mul_of_nonneg_right hk.le (gap_nonneg hm k))
  have hsum_gap : Tendsto (fun M => ∑ k ∈ Finset.range M, gap y k) atTop atTop := by
    simpa only [sum_gap] using tendsto_span hy
  have hsum : (fun M => ∑ k ∈ Finset.range M, f k) =o[atTop] (fun M => y M - y 0) := by
    simpa only [sum_gap] using hs.sum_range (show 0 ≤ gap y from gap_nonneg hm) hsum_gap
  have hcast :
      (fun M => y M - y 0) =O[atTop] (fun M => (↑(y M - y 0) : ℂ)) :=
    isBigO_of_le _ fun M => by rw [Complex.norm_real]
  exact (hsum.trans_isBigO hcast).tendsto_div_nhds_zero

/-- Gap-weighted averages of a null sample error tend to zero. -/
theorem tendsto_average_zero {y : ℕ → ℝ} (hm : StrictMono y)
    (hy : Tendsto y atTop atTop) {e : ℕ → ℂ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (average y e) atTop (𝓝 0) := by
  unfold average
  refine tendsto_normalized_sum_zero hm hy (tendsto_zero_iff_norm_tendsto_zero.mp he) ?_
  intro k
  simpa only [norm_mul, Complex.norm_of_nonneg (gap_nonneg hm k)] using
    (mul_comm (gap y k) ‖e k‖).le

/-- Gap-weighted averages preserve the limit of a convergent sample sequence. -/
theorem tendsto_average {y : ℕ → ℝ} (hm : StrictMono y)
    (hy : Tendsto y atTop atTop) {a : ℕ → ℂ} {z : ℂ} (ha : Tendsto a atTop (𝓝 z)) :
    Tendsto (average y a) atTop (𝓝 z) := by
  have hsub : Tendsto (fun k => a k - z) atTop (𝓝 0) := by
    simpa only [sub_self] using ha.sub_const z
  have ht : Tendsto (fun M => average y (fun k => a k - z) M + z) atTop (𝓝 z) := by
    simpa only [zero_add] using (tendsto_average_zero hm hy hsub).add
      (show Tendsto (fun _ : ℕ => z) atTop (𝓝 z) from tendsto_const_nhds)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with M hM
  calc
    average y (fun k => a k - z) M + z =
        average y (fun k => a k - z) M + average y (fun _ => z) M := by
      rw [average_const hm hM z]
    _ = average y a M := by rw [← average_add]; simp only [sub_add_cancel]

/-- A single phase has limiting average one at frequency zero and zero at every
other frequency. The gaps need only tend to zero. -/
theorem tendsto_average_phase {y : ℕ → ℝ} (hm : StrictMono y)
    (hy : Tendsto y atTop atTop) (hgap : Tendsto (gap y) atTop (𝓝 0)) (μ : ℝ) :
    Tendsto (average y (fun k => phase μ (y k))) atTop (𝓝 (if μ = 0 then 1 else 0)) := by
  by_cases hμ : μ = 0
  · simp only [hμ, if_pos rfl, phase, Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero]
    exact tendsto_average hm hy tendsto_const_nhds
  rw [if_neg hμ]
  let c : ℂ := Complex.I * (μ : ℂ)
  have hc : c ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hμ)
  let P : ℝ → ℂ := fun x => phase μ x / c
  let r : ℕ → ℂ := fun k => (gap y k : ℂ) * phase μ (y k) - (P (y (k + 1)) - P (y k))
  have hcont : Continuous (phase μ) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.const_mul c)
  have hint (a b : ℝ) : (∫ t in a..b, phase μ t) = P b - P a := by
    simpa only [P, phase, c, sub_div] using (integral_exp_mul_complex (a := a) (b := b) hc)
  have hphase_sub (u t : ℝ) : ‖phase μ u - phase μ t‖ ≤ ‖μ‖ * ‖t - u‖ := by
    have hfactor : phase μ t - phase μ u =
        phase μ u * (Complex.exp (Complex.I * (↑(μ * (t - u)) : ℂ)) - 1) := by
      rw [mul_sub, mul_one]
      apply congrArg (fun z : ℂ => z - phase μ u)
      simp only [phase, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_sub]
      apply congrArg Complex.exp
      ring
    rw [norm_sub_rev, hfactor, norm_mul, norm_phase, one_mul, ← norm_mul]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le
  have hrbound (k : ℕ) : ‖r k‖ ≤ (‖μ‖ * gap y k) * gap y k := by
    have hle : y k ≤ y (k + 1) := (hm (Nat.lt_succ_self k)).le
    have heq : r k = ∫ t in y k..y (k + 1), phase μ (y k) - phase μ t := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const (c := phase μ (y k)))
        (hcont.intervalIntegrable (y k) (y (k + 1))),
        intervalIntegral.integral_const, Complex.real_smul, hint] <;> rfl
    have hpoint : ∀ t ∈ Set.uIoc (y k) (y (k + 1)),
        ‖phase μ (y k) - phase μ t‖ ≤ ‖μ‖ * gap y k := by
      intro t ht
      rw [Set.uIoc_of_le hle] at ht
      apply (hphase_sub (y k) t).trans
      rw [Real.norm_of_nonneg (sub_nonneg.mpr ht.1.le)]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 (y k)) (norm_nonneg μ)
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    change _ ≤ (‖μ‖ * gap y k) * |gap y k| at hbound
    rw [abs_of_nonneg (gap_nonneg hm k)] at hbound
    rw [heq]
    exact hbound
  have hb : Tendsto (fun k => ‖μ‖ * gap y k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hgap.const_mul ‖μ‖
  have hR := tendsto_normalized_sum_zero hm hy hb hrbound
  have hP : Tendsto (fun M => (P (y M) - P (y 0)) / (↑(y M - y 0) : ℂ)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) ?_ ((tendsto_span hy).const_div_atTop (2 / ‖c‖))
    intro M
    have hspan : 0 ≤ y M - y 0 := sub_nonneg.mpr (hm.monotone (Nat.zero_le M))
    rw [norm_div, Complex.norm_of_nonneg hspan]
    apply div_le_div_of_nonneg_right _ hspan
    calc
      ‖P (y M) - P (y 0)‖ ≤ ‖P (y M)‖ + ‖P (y 0)‖ := norm_sub_le _ _
      _ = 2 / ‖c‖ := by simp only [P, norm_div, norm_phase, ← add_div, one_add_one_eq_two]
  -- The primitive increments telescope across all intervals.
  have ht := hR.add hP
  rw [zero_add] at ht
  apply ht.congr
  intro M
  unfold average
  rw [← add_div]
  apply congrArg (fun z : ℂ => z / (↑(y M - y 0) : ℂ))
  simp only [r, Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => P (y k)), sub_add_cancel]

private theorem tendsto_average_series {ι : Type*} {y : ℕ → ℝ} (hm : StrictMono y)
    (hy : Tendsto y atTop atTop) {a : ι → ℂ} (ha : Summable (fun i => ‖a i‖))
    {mode : ℕ → ι → ℂ} (hmode : ∀ k i, ‖mode k i‖ ≤ 1) {b : ι → ℂ}
    (hterm : ∀ i, Tendsto (fun M => a i * average y (fun k => mode k i) M) atTop (𝓝 (b i)))
    {e : ℕ → ℂ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (average y (fun k => (∑' i, a i * mode k i) + e k)) atTop (𝓝 (∑' i, b i)) := by
  have havg (M : ℕ) (i : ι) : ‖average y (fun k => mode k i) M‖ ≤ 1 := by
    by_cases hM : M = 0
    · simp [hM, average]
    have hd : 0 < y M - y 0 := sub_pos.mpr (hm (Nat.pos_of_ne_zero hM))
    rw [average, norm_div, Complex.norm_of_nonneg hd.le, div_le_iff₀ hd, one_mul, ← sum_gap y M]
    refine norm_sum_le_of_le _ fun k _ => ?_
    rw [norm_mul, Complex.norm_of_nonneg (gap_nonneg hm k)]
    exact mul_le_of_le_one_right (gap_nonneg hm k) (hmode k i)
  have hdom : ∀ᶠ M in atTop, ∀ i, ‖a i * average y (fun k => mode k i) M‖ ≤ ‖a i‖ :=
    Eventually.of_forall fun M i => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (havg M i)
  have hexchange (M : ℕ) :
      (∑' i, a i * average y (fun k => mode k i) M) =
        average y (fun k => ∑' i, a i * mode k i) M := by
    let f : ℕ → ι → ℂ := fun k i => (gap y k : ℂ) * (a i * mode k i)
    have hf (k : ℕ) : Summable (f k) := by
      have hk : Summable (fun i => a i * mode k i) := ha.of_norm_bounded fun i => by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hmode k i)
      exact hk.mul_left _
    calc
      (∑' i, a i * average y (fun k => mode k i) M) =
          ∑' i, (∑ k ∈ Finset.range M, f k i) / (↑(y M - y 0) : ℂ) := by
        apply tsum_congr
        intro i
        rw [average, ← mul_div_assoc, Finset.mul_sum]
        apply congrArg (fun z : ℂ => z / (↑(y M - y 0) : ℂ))
        refine Finset.sum_congr rfl fun k _ => ?_
        exact mul_left_comm _ _ _
      _ = (∑ k ∈ Finset.range M, ∑' i, f k i) / (↑(y M - y 0) : ℂ) := by
        rw [tsum_div_const, Summable.tsum_finsetSum (fun k _ => hf k)]
      _ = _ := by simp only [average, f, tsum_mul_left]
  have hseries :
      Tendsto (average y (fun k => ∑' i, a i * mode k i)) atTop (𝓝 (∑' i, b i)) :=
    (tendsto_tsum_of_dominated_convergence ha hterm hdom).congr hexchange
  have ht := hseries.add (tendsto_average_zero hm hy he)
  rw [add_zero] at ht
  exact ht.congr fun M => (average_add y (fun k => ∑' i, a i * mode k i) e M).symm

/-- Recover the sum of the coefficients at `ν` from samples of an absolutely
summable exponential series with an additive error tending to zero. -/
theorem tendsto_average_modulated_series {ι : Type*} {y : ℕ → ℝ} (hm : StrictMono y)
    (hy : Tendsto y atTop atTop) (hgap : Tendsto (gap y) atTop (𝓝 0))
    (a : ι → ℂ) (freq : ι → ℝ) (ha : Summable (fun i => ‖a i‖)) (ν : ℝ)
    {s e : ℕ → ℂ} (he : Tendsto e atTop (𝓝 0))
    (hs : ∀ k, s k = (∑' i, a i * phase (freq i) (y k)) + e k) :
    Tendsto (average y (fun k => s k * phase (-ν) (y k))) atTop
      (𝓝 (∑' i, if freq i = ν then a i else 0)) := by
  have hterm (i : ι) :
      Tendsto (fun M => a i * average y (fun k => phase (freq i - ν) (y k)) M) atTop
        (𝓝 (if freq i = ν then a i else 0)) := by
    have ht := (tendsto_average_phase hm hy hgap (freq i - ν)).const_mul (a i)
    by_cases hi : freq i = ν
    · simpa only [hi, sub_self, ite_true, mul_one] using ht
    · simpa only [ite_eq_right hi, ite_eq_right (sub_ne_zero.mpr hi), mul_zero] using ht
  have herror : Tendsto (fun k => e k * phase (-ν) (y k)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_mul, norm_phase, mul_one] using tendsto_zero_iff_norm_tendsto_zero.mp he
  have hmodulation (i : ι) (k : ℕ) :
      phase (freq i) (y k) * phase (-ν) (y k) = phase (freq i - ν) (y k) := by
    simp only [phase, ← Complex.exp_add, Complex.ofReal_sub, Complex.ofReal_neg]
    apply congrArg Complex.exp
    ring
  have ht := tendsto_average_series hm hy ha
    (mode := fun k i => phase (freq i - ν) (y k))
    (fun k i => (norm_phase (freq i - ν) (y k)).le) hterm herror
  apply ht.congr
  intro M
  apply congrArg (fun g : ℕ → ℂ => average y g M)
  funext k
  rw [hs k, add_mul, ← tsum_mul_right]
  apply congrArg (fun z : ℂ => z + e k * phase (-ν) (y k))
  apply tsum_congr
  intro i
  rw [mul_assoc, hmodulation]

private theorem tendsto_average_congr {y : ℕ → ℝ} (hm : StrictMono y)
    (hy : Tendsto y atTop atTop) {f g : ℕ → ℂ} {L : ℂ}
    (hfg : f =ᶠ[atTop] g) (hf : Tendsto (average y f) atTop (𝓝 L)) :
    Tendsto (average y g) atTop (𝓝 L) := by
  have hzero : Tendsto (fun k => g k - f k) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0) := tendsto_const_nhds
    apply hconst.congr'
    filter_upwards [hfg] with k hk
    change f k = g k at hk
    exact (sub_eq_zero.mpr hk.symm).symm
  have ht := hf.add (tendsto_average_zero hm hy hzero)
  rw [add_zero] at ht
  refine ht.congr fun M => ?_
  rw [← average_add]
  apply congrArg (fun s : ℕ → ℂ => average y s M)
  funext k
  rw [add_comm (f k), sub_add_cancel]

/-- On a mesh with vanishing gaps, the gap-weighted average of an absolutely
summable series demodulated by `w` recovers the sum of coefficients at `w` when
all exponents have real part at most `w.re`. A null sample error preserves the
limit. -/
theorem tendsto_average_closed_strip_series {ι : Type*} {y : ℕ → ℝ} (hm : StrictMono y)
    (hy : Tendsto y atTop atTop) (hgap : Tendsto (gap y) atTop (𝓝 0))
    (a z : ι → ℂ) (ha : Summable (fun i => ‖a i‖)) (w : ℂ) (hz : ∀ i, (z i).re ≤ w.re)
    {e : ℕ → ℂ} (he : Tendsto e atTop (𝓝 0)) :
    Tendsto (average y (fun k => (∑' i, a i * Complex.exp ((y k : ℂ) * (z i - w))) + e k))
      atTop (𝓝 (∑' i, if z i = w then a i else 0)) := by
  -- Use nonnegative sample arguments for the uniform bound on the modes.
  let mode : ℕ → ι → ℂ := fun k i => Complex.exp ((↑(max (y k) 0) : ℂ) * (z i - w))
  have hclamp : (fun k => max (y k) 0) =ᶠ[atTop] y :=
    (hy.eventually (eventually_ge_atTop (0 : ℝ))).mono fun _ hk => max_eq_left hk
  have hmesh : Tendsto (fun k => max (y k) 0) atTop atTop := hy.congr' hclamp.symm
  have hnorm (x : ℝ) (i : ι) :
      ‖Complex.exp ((x : ℂ) * (z i - w))‖ = Real.exp (x * ((z i).re - w.re)) := by
    simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, zero_mul, sub_zero]
  have hbound (k : ℕ) (i : ι) : ‖mode k i‖ ≤ 1 := by
    dsimp only [mode]
    rw [hnorm, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonneg_of_nonpos (le_max_right _ _) (sub_nonpos.mpr (hz i))
  have haverage (i : ι) :
      Tendsto (average y (fun k => mode k i)) atTop (𝓝 (if z i = w then 1 else 0)) := by
    by_cases hi : z i = w
    · rw [if_pos hi]
      apply tendsto_average hm hy
      simpa only [mode, hi, sub_self, mul_zero, Complex.exp_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
    rw [if_neg hi]
    by_cases hre : (z i).re = w.re
    · have him : (z i).im ≠ w.im := fun h => hi (Complex.ext hre h)
      have hdiff : z i - w = Complex.I * (↑((z i).im - w.im) : ℂ) := by
        apply Complex.ext
        · simp only [Complex.sub_re, hre, sub_self, Complex.I_mul_re, Complex.ofReal_im,
            neg_zero]
        · simp only [Complex.sub_im, Complex.I_mul_im, Complex.ofReal_re]
      have ht := tendsto_average_phase hm hy hgap ((z i).im - w.im)
      rw [if_neg (sub_ne_zero.mpr him)] at ht
      refine tendsto_average_congr hm hy ?_ ht
      filter_upwards [hclamp] with k hk
      change max (y k) 0 = y k at hk
      change phase ((z i).im - w.im) (y k) =
        Complex.exp ((↑(max (y k) 0) : ℂ) * (z i - w))
      rw [hk, hdiff, phase, mul_comm (y k : ℂ)]
    · have hdecay : Tendsto (fun k => max (y k) 0 * ((z i).re - w.re)) atTop atBot :=
        hmesh.atTop_mul_const_of_neg (sub_neg.mpr (lt_of_le_of_ne (hz i) hre))
      apply tendsto_average_zero hm hy
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simp only [mode, hnorm]
      exact Real.tendsto_exp_atBot.comp hdecay
  have hterm (i : ι) :
      Tendsto (fun M => a i * average y (fun k => mode k i) M) atTop
        (𝓝 (if z i = w then a i else 0)) := by
    simpa only [mul_ite, mul_one, mul_zero] using (haverage i).const_mul (a i)
  have ht := tendsto_average_series hm hy ha (mode := mode) hbound hterm he
  refine tendsto_average_congr hm hy ?_ ht
  filter_upwards [hclamp] with k hk
  change max (y k) 0 = y k at hk
  change (∑' i, a i * mode k i) + e k =
    (∑' i, a i * Complex.exp ((y k : ℂ) * (z i - w))) + e k
  simp only [mode, hk]

end GapWeightedFourier
