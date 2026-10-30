/- GID: D5/S3/Entropy/BinaryEntropyLogIntegral
   generality: G
   mirror-B: D5/B/S3/Entropy/BinaryEntropyLogIntegral
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact logarithmic integral representation of square-root binary entropy on the closed unit interval. -/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Entropy.BinaryEntropyLogIntegral
open Set Filter MeasureTheory
open scoped Topology

private def entropyPrimitive (x s : ℝ) : ℝ :=
  let y := Real.sqrt (1 + s)
  let r := Real.sqrt (1 - x)
  2 * (y * Real.log (s + x)) - 2 * ((s * Real.log s) / (y + 1)) -
    4 * Real.log (y + 1) + (2 * r) * (Real.log (y + r) - Real.log (y - r))

private def rawPrimitive (x s : ℝ) : ℝ :=
  let y := Real.sqrt (1 + s)
  let r := Real.sqrt (1 - x)
  2 * (y * (Real.log (s + x) - Real.log s)) +
    (2 * r) * (Real.log (y + r) - Real.log (y - r)) -
    2 * (Real.log (y + 1) - Real.log (y - 1))

private lemma sqrt_data {x s : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) :
    let r := Real.sqrt (1 - x)
    let y := Real.sqrt (1 + s)
    r ^ 2 = 1 - x ∧ 0 ≤ r ∧ r < 1 ∧ y ^ 2 = 1 + s ∧ 1 < y := by
  have hr2 := Real.sq_sqrt (sub_nonneg.mpr hx.2)
  have hr := Real.sqrt_nonneg (1 - x)
  have hy2 := Real.sq_sqrt (show 0 ≤ 1 + s by linarith)
  have hy := Real.sqrt_nonneg (1 + s)
  dsimp only
  exact ⟨hr2, hr, by nlinarith, hy2, by nlinarith⟩

private lemma primitive_eq_raw {x s : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) :
    entropyPrimitive x s = rawPrimitive x s := by
  obtain ⟨_, _, _, hy2, hy1⟩ := sqrt_data hx hs
  let y := Real.sqrt (1 + s)
  have hyp : 0 < y + 1 := by dsimp [y]; linarith
  have hym : 0 < y - 1 := by dsimp [y]; linarith
  have hfactor : (y - 1) * (y + 1) = s := by dsimp [y]; nlinarith
  have hlog : Real.log s = Real.log (y - 1) + Real.log (y + 1) := by
    rw [← Real.log_mul hym.ne' hyp.ne', hfactor]
  have hsid : s = y ^ 2 - 1 := by dsimp [y]; linarith
  dsimp only [entropyPrimitive, rawPrimitive]
  change 2 * (y * Real.log (s + x)) - 2 * ((s * Real.log s) / (y + 1)) -
      4 * Real.log (y + 1) + _ =
    2 * (y * (Real.log (s + x) - Real.log s)) + _ -
      2 * (Real.log (y + 1) - Real.log (y - 1))
  rw [hlog]
  field_simp [hyp.ne']
  rw [hsid]
  ring

private lemma primitive_continuousAt_zero {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ContinuousAt (entropyPrimitive x) 0 := by
  let r := Real.sqrt (1 - x)
  have hr2 : r ^ 2 = 1 - x := Real.sq_sqrt (sub_nonneg.mpr hx.2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r < 1 := by nlinarith [hx.1]
  have hy : ContinuousAt (fun s : ℝ => Real.sqrt (1 + s)) 0 := by fun_prop
  have hlx := (continuousAt_id.add_const x).log (by simpa using hx.1.ne')
  have hmlog : ContinuousAt (fun s : ℝ => s * Real.log s) 0 :=
    Real.continuous_mul_log.continuousAt
  have hdiv := hmlog.div (hy.add_const 1) (by norm_num)
  have hlp := (hy.add_const r).log (by simpa using (show 1 + r ≠ 0 by linarith))
  have hlm := (hy.sub_const r).log (by simpa using (sub_pos.mpr hr1).ne')
  exact ((((hy.mul hlx).const_mul 2).sub (hdiv.const_mul 2)).sub
    (((hy.add_const 1).log (by norm_num)).const_mul 4)).add
    ((hlp.sub hlm).const_mul (2 * r))

private lemma raw_hasDerivAt {x s : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) :
    HasDerivAt (rawPrimitive x)
      (Real.log (1 + x / s) / Real.sqrt (1 + s)) s := by
  obtain ⟨hr2, hr, hr1, hy2, hy1⟩ := sqrt_data hx hs
  let y := Real.sqrt (1 + s)
  let r := Real.sqrt (1 - x)
  have hy : 0 < y := by dsimp [y]; linarith
  have hsp : 0 < s + x := by linarith [hx.1]
  have hpr : 0 < y + r := by dsimp [y, r]; linarith
  have hmr : 0 < y - r := by dsimp [y, r]; linarith
  have hp1 : 0 < y + 1 := by linarith
  have hm1 : 0 < y - 1 := by dsimp [y]; linarith
  have hdy : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t)) (1 / (2 * y)) s := by
    simpa using ((hasDerivAt_id s).const_add 1).sqrt (by linarith : 1 + s ≠ 0)
  have hlogx := ((hasDerivAt_id s).add_const x).log hsp.ne'
  have hlogs := (hasDerivAt_id s).log hs.ne'
  have hlogpr := (hdy.add_const r).log hpr.ne'
  have hlogmr := (hdy.sub_const r).log hmr.ne'
  have hlogp1 := (hdy.add_const 1).log hp1.ne'
  have hlogm1 := (hdy.sub_const 1).log hm1.ne'
  have h := (((hdy.mul (hlogx.sub hlogs)).const_mul 2).add
    ((hlogpr.sub hlogmr).const_mul (2 * r))).sub ((hlogp1.sub hlogm1).const_mul 2)
  have hlog : Real.log (1 + x / s) = Real.log (s + x) - Real.log s := by
    rw [show 1 + x / s = (s + x) / s by field_simp [hs.ne']; ring]
    exact Real.log_div hsp.ne' hs.ne'
  have hsid : s = y ^ 2 - 1 := by dsimp [y]; linarith
  have hxid : x = 1 - r ^ 2 := by dsimp [r]; linarith
  convert h using 1
  rw [hlog]
  field_simp [hy.ne', hs.ne', hsp.ne', hpr.ne', hmr.ne', hp1.ne', hm1.ne']
  rw [hsid, hxid]
  ring

private lemma primitive_hasDerivAt {x s : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hs : 0 < s) :
    HasDerivAt (entropyPrimitive x)
      (Real.log (1 + x / s) / Real.sqrt (1 + s)) s := by
  apply (raw_hasDerivAt hx hs).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  exact primitive_eq_raw hx ht

private lemma sqrt_div_tendsto :
    Tendsto (fun s : ℝ => Real.sqrt (1 + s) / s) atTop (𝓝 0) := by
  have htop : Tendsto (fun s : ℝ => Real.sqrt (1 + s)) atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    simpa [add_comm] using (tendsto_id.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hi := tendsto_inv_atTop_zero.comp htop
  have h : Tendsto (fun s : ℝ => (1 + s⁻¹) * (Real.sqrt (1 + s))⁻¹)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.add tendsto_inv_atTop_zero).mul hi
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  have hy : 0 < Real.sqrt (1 + s) := Real.sqrt_pos.mpr (by linarith)
  have hy2 := Real.sq_sqrt (show 0 ≤ 1 + s by linarith)
  field_simp [hs.ne', hy.ne']
  nlinarith

private lemma log_gap_tendsto (c : ℝ) :
    Tendsto (fun s : ℝ => Real.log (Real.sqrt (1 + s) + c) -
      Real.log (Real.sqrt (1 + s) - c)) atTop (𝓝 0) := by
  have htop : Tendsto (fun s : ℝ => Real.sqrt (1 + s)) atTop atTop := by
    apply Real.tendsto_sqrt_atTop.comp
    simpa [add_comm] using (tendsto_id.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  have hp := (Real.tendsto_log_comp_add_sub_log c).comp htop
  have hm := (Real.tendsto_log_comp_add_sub_log (-c)).comp htop
  convert hp.sub hm using 1
  · funext s
    dsimp only [Function.comp_def]
    ring
  · norm_num

private lemma primitive_tendsto {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    Tendsto (entropyPrimitive x) atTop (𝓝 0) := by
  have hfirst : Tendsto (fun s : ℝ =>
      2 * (Real.sqrt (1 + s) * Real.log (1 + x / s))) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun s : ℝ => (2 * x) * (Real.sqrt (1 + s) / s))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      exact mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg _)
        (Real.log_nonneg (by have := div_nonneg hx.1.le hs.le; linarith)))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
      have hp : 0 < 1 + x / s := by positivity
      have hl := Real.log_le_sub_one_of_pos hp
      have hh := mul_le_mul_of_nonneg_left hl
        (show 0 ≤ 2 * Real.sqrt (1 + s) by positivity)
      convert hh using 1 <;> ring
    · simpa using sqrt_div_tendsto.const_mul (2 * x)
  let r := Real.sqrt (1 - x)
  have hcomb : Tendsto (fun s : ℝ =>
      2 * (Real.sqrt (1 + s) * Real.log (1 + x / s)) +
      (2 * r) * (Real.log (Real.sqrt (1 + s) + r) - Real.log (Real.sqrt (1 + s) - r)) -
      2 * (Real.log (Real.sqrt (1 + s) + 1) - Real.log (Real.sqrt (1 + s) - 1)))
      atTop (𝓝 0) := by
    simpa using (hfirst.add ((log_gap_tendsto r).const_mul (2 * r))).sub
      ((log_gap_tendsto 1).const_mul 2)
  have hraw : Tendsto (rawPrimitive x) atTop (𝓝 0) := by
    apply hcomb.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    have hsp : 0 < s + x := by linarith [hx.1]
    have hlog : Real.log (1 + x / s) = Real.log (s + x) - Real.log s := by
      rw [show 1 + x / s = (s + x) / s by field_simp [hs.ne']; ring]
      exact Real.log_div hsp.ne' hs.ne'
    simp only [rawPrimitive, hlog]
  apply hraw.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  exact (primitive_eq_raw hx hs).symm

private lemma primitive_zero {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    entropyPrimitive x 0 = -4 * Real.binEntropy ((1 + Real.sqrt (1 - x)) / 2) := by
  let r := Real.sqrt (1 - x)
  have hr2 : r ^ 2 = 1 - x := Real.sq_sqrt (sub_nonneg.mpr hx.2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r < 1 := by nlinarith [hx.1]
  have hp : 0 < 1 + r := by linarith
  have hm : 0 < 1 - r := by linarith
  have hlog : Real.log x = Real.log (1 + r) + Real.log (1 - r) := by
    rw [← Real.log_mul hp.ne' hm.ne']
    congr 1
    nlinarith
  have hhalf : 1 - (1 + r) / 2 = (1 - r) / 2 := by ring
  simp only [entropyPrimitive, zero_add, Real.sqrt_one, zero_mul, zero_div, sub_zero]
  change 2 * (1 * Real.log x) - 4 * Real.log (1 + 1) +
      (2 * r) * (Real.log (1 + r) - Real.log (1 - r)) =
    -4 * Real.binEntropy ((1 + r) / 2)
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hhalf]
  simp only [Real.negMulLog_def]
  rw [Real.log_div hp.ne' (by norm_num), Real.log_div hm.ne' (by norm_num), hlog]
  norm_num
  <;> ring

/-- The closed-domain logarithmic integral formula for the actual binary entropy.
The integrand is absolutely integrable, including x=0 and x=1. -/
theorem binEntropy_sqrt_log_integral {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    IntegrableOn (fun s : ℝ => Real.log (1 + x / s) / Real.sqrt (1 + s)) (Ioi 0) ∧
      Real.binEntropy ((1 + Real.sqrt (1 - x)) / 2) =
        (1 / 4 : ℝ) * ∫ s in Ioi (0 : ℝ), Real.log (1 + x / s) / Real.sqrt (1 + s) := by
  by_cases hx0 : x = 0
  · subst x
    simp
  have hx' : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hx.1 hx0.symm, hx.2⟩
  have hc := (primitive_continuousAt_zero hx').continuousWithinAt (s := Ici (0 : ℝ))
  have hd := fun s (hs : s ∈ Ioi (0 : ℝ)) => primitive_hasDerivAt hx' hs
  have hp : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ Real.log (1 + x / s) / Real.sqrt (1 + s) := by
    intro s hs
    apply div_nonneg _ (Real.sqrt_nonneg _)
    apply Real.log_nonneg
    have h := div_nonneg hx.1 hs.le
    linarith
  have ht := primitive_tendsto hx'
  refine ⟨integrableOn_Ioi_deriv_of_nonneg hc hd hp ht, ?_⟩
  have he := integral_Ioi_of_hasDerivAt_of_nonneg hc hd hp ht
  rw [primitive_zero hx'] at he
  linarith

#print axioms binEntropy_sqrt_log_integral
end D5.S3.Entropy.BinaryEntropyLogIntegral
