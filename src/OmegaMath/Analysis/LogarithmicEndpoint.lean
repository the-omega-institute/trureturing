import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
Omega original.

Logarithmic asymptotics from endpoint derivative limits.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set
open scoped Topology

namespace Omega

theorem tendsto_div_log_of_mul_deriv {F : ℝ → ℝ} {q : ℝ}
    (hF : ∀ᶠ x in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ F x)
    (hq : Tendsto (fun x => x * deriv F x) (𝓝[>] 0) (𝓝 q)) :
    Tendsto (fun x => F x / Real.log x) (𝓝[>] 0) (𝓝 q) := by
  rw [tendsto_order]
  have hcompare (l u : ℝ) (hl : l < q) (hu : q < u) :
      (∀ᶠ x in 𝓝[>] (0 : ℝ), l < F x / Real.log x) ∧
        (∀ᶠ x in 𝓝[>] (0 : ℝ), F x / Real.log x < u) := by
    let m := (l + q) / 2
    let n := (q + u) / 2
    have hmn : ∀ᶠ x in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ F x ∧
        m < x * deriv F x ∧ x * deriv F x < n :=
      hF.and (((tendsto_order.mp hq).1 m (by dsimp [m]; linarith)).and
        ((tendsto_order.mp hq).2 n (by dsimp [n]; linarith)))
    obtain ⟨b, hb, hnear⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hmn
    change 0 < b at hb
    let r := b / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrb : r < b := by dsimp [r]; linarith
    have hinv := tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
    have hlimit (k : ℝ) : Tendsto (fun x => k + (F r - k * Real.log r) / Real.log x)
        (𝓝[>] 0) (𝓝 k) := by
      simpa [div_eq_mul_inv, Function.comp_def] using
        (hinv.const_mul (F r - k * Real.log r)).const_add k
    have hc : ∀ᶠ x in 𝓝[>] (0 : ℝ),
        m + (F r - m * Real.log r) / Real.log x < F x / Real.log x ∧
          F x / Real.log x < n + (F r - n * Real.log r) / Real.log x := by
      filter_upwards [Ioo_mem_nhdsGT hr, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx hx'
      have hfc : ContinuousOn F (Icc x r) := fun y hy =>
        (hnear ⟨hx.1.trans_le hy.1, hy.2.trans_lt hrb⟩).1.continuousAt.continuousWithinAt
      have hgc : ContinuousOn Real.log (Icc x r) := fun y hy =>
        (Real.continuousAt_log (hx.1.trans_le hy.1).ne').continuousWithinAt
      obtain ⟨c, hc, he⟩ := exists_ratio_hasDerivAt_eq_ratio_slope F (deriv F) hx.2 hfc
        (fun y hy => (hnear ⟨hx.1.trans hy.1, hy.2.trans hrb⟩).1.hasDerivAt) Real.log (fun y => y⁻¹)
        hgc (fun y hy => Real.hasDerivAt_log (hx.1.trans hy.1).ne')
      have hcp : 0 < c := hx.1.trans hc.1
      have hcm := (hnear ⟨hcp, hc.2.trans hrb⟩).2.1
      have hcn := (hnear ⟨hcp, hc.2.trans hrb⟩).2.2
      have hlog := Real.log_lt_log hx.1 hx.2
      have hxlog := Real.log_neg hx'.1 hx'.2
      have he' : (Real.log r - Real.log x) * (c * deriv F c) = F r - F x := by
        calc
          _ = c * ((Real.log r - Real.log x) * deriv F c) := by ring
          _ = F r - F x := by rw [he]; field_simp
      have hfrac (k : ℝ) : k + (F r - k * Real.log r) / Real.log x =
          (k * Real.log x + (F r - k * Real.log r)) / Real.log x := by
        field_simp [hxlog.ne]
      simp only [hfrac, div_lt_div_right_of_neg hxlog]
      constructor
      · nlinarith [mul_pos (sub_pos.mpr hlog) (sub_pos.mpr hcm)]
      · nlinarith [mul_pos (sub_pos.mpr hlog) (sub_pos.mpr hcn)]
    constructor
    · filter_upwards [(tendsto_order.mp (hlimit m)).1 l (by dsimp [m]; linarith), hc]
        with x hx hxc using hx.trans hxc.1
    · filter_upwards [(tendsto_order.mp (hlimit n)).2 u (by dsimp [n]; linarith), hc]
        with x hx hxc using hxc.2.trans hx
  exact ⟨fun l hl => (hcompare l (q + 1) hl (by linarith)).1,
    fun u hu => (hcompare (q - 1) u (by linarith) hu).2⟩

/-- A weighted derivative with a logarithmic leading term determines the normalized
function's leading term at the endpoint. -/
theorem tendsto_sub_div_mul_log_of_weighted_deriv {F p : ℝ → ℝ} {b q : ℝ}
    (hF : ∀ᶠ x in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ F x)
    (hF₀ : Tendsto F (𝓝[>] 0) (𝓝 b)) (hp : Tendsto p (𝓝[>] 0) (𝓝 1))
    (hz : ∀ᶠ x in 𝓝[>] (0 : ℝ), DifferentiableAt ℝ (fun t => p t * deriv F t) x)
    (hq : Tendsto (fun x => x * deriv (fun t => p t * deriv F t) x) (𝓝[>] 0) (𝓝 q)) :
    Tendsto (fun x => (F x - b) / (x * Real.log x)) (𝓝[>] 0) (𝓝 q) := by
  have hr := tendsto_div_log_of_mul_deriv hz hq
  have hi := tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have hden : Tendsto (fun x => p x * (1 + (Real.log x)⁻¹)) (𝓝[>] 0) (𝓝 1) := by
    simpa using hp.mul (hi.const_add 1)
  have hratio : Tendsto (fun x => deriv F x / (Real.log x + 1)) (𝓝[>] 0) (𝓝 q) := by
    have hh := hr.div hden one_ne_zero
    simp only [div_one] at hh
    refine Tendsto.congr' ?_ hh
    filter_upwards [(tendsto_order.mp hp).1 0 zero_lt_one,
      Ioo_mem_nhdsGT (show (0 : ℝ) < Real.exp (-2) by positivity)] with x hx hxr
    have hl : Real.log x < -2 := (Real.log_lt_iff_lt_exp hxr.1).2 hxr.2
    have hlog : Real.log x ≠ 0 := by linarith
    have hlog1 : Real.log x + 1 ≠ 0 := by linarith
    simp only [Pi.div_apply]
    field_simp [hx.ne', hlog, hlog1]
  apply HasDerivAt.lhopital_zero_nhdsGT (f' := deriv F) (g' := fun x => Real.log x + 1)
  · exact hF.mono fun x hx => hx.hasDerivAt.sub_const b
  · filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := (show 0 < x from hx).ne'
    convert (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0) using 1
    · rfl
    · simp [id, hx0]
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.exp (-2) by positivity)] with x hx
    have hl : Real.log x < -2 := (Real.log_lt_iff_lt_exp hx.1).2 hx.2
    linarith
  · simpa using hF₀.sub (tendsto_const_nhds (x := b))
  · have hc : Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] 0) (𝓝 (0 * Real.log 0)) :=
      Real.continuous_mul_log.continuousAt.continuousWithinAt
    simpa using hc
  · exact hratio

end Omega
