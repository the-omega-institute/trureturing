/- GID: D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/FirstOrderGap
   generality: G
   mirror-B: D5/B/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/FirstOrderGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv, mathlib/module/Mathlib.Analysis.Convex.SpecificFunctions.Basic, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Slope]
   utility: none
   digest: Convex chord integration and a positive derivative difference separate radial norm and evaluation powers for every finite p below q. -/

import D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Radial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Weighted radial moments, a convex power bound, and strict separation near zero. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Radial
namespace D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap

private lemma weight_moment {b : ℝ} (hb : -1 < b) :
    IntervalIntegrable (fun x : ℝ => x * (1-x^2)^b) volume 0 1 ∧
    (∫ x in (0:ℝ)..1, x * (1-x^2)^b) = 1 / (2*(b+1)) := by
  have hc : ContinuousOn (fun x : ℝ => 1-x^2) (uIcc (0:ℝ) 1) := by fun_prop
  have hd : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1),
      HasDerivAt (fun x : ℝ => 1-x^2) (-2*x) x := by
    intro x hx
    convert (hasDerivAt_const x (1:ℝ)).sub ((hasDerivAt_id x).pow 2) using 1
    · ext y
      rfl
    · simp only [id_eq]
      ring
  have hn : ∀ x ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1), -2*x ≤ 0 := by
    intro x hx
    norm_num at hx
    linarith [hx.1]
  have hi := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonpos
    (g := fun u : ℝ => u^b) hc hd hn).2 (by
      simpa using (intervalIntegral.intervalIntegrable_rpow' hb :
        IntervalIntegrable (fun u : ℝ => u^b) volume 1 0))
  have hie : IntervalIntegrable (fun x : ℝ => x*(1-x^2)^b) volume 0 1 := by
    convert hi.const_mul (-1/2:ℝ) using 1
    ext x
    simp only [Function.comp_def]
    ring
  refine ⟨hie, ?_⟩
  have he := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos
    (g := fun u : ℝ => u^b) hc hd hn
  simp only [Function.comp_def] at he
  have hr := integral_rpow (a := (1:ℝ)) (b := 0) (Or.inl hb)
  have hb0 : b+1 ≠ 0 := by linarith
  norm_num only [zero_pow, one_pow, sub_zero, sub_self] at he
  rw [hr, Real.one_rpow, Real.zero_rpow hb0] at he
  have hscale : (∫ x in (0:ℝ)..1, (1-x^2)^b*(-2*x)) =
      -2 * (∫ x in (0:ℝ)..1, x*(1-x^2)^b) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext x
    ring
  rw [hscale] at he
  field_simp [hb0] at he ⊢
  nlinarith

private lemma weight_square {b : ℝ} (hb : 0 < b) :
    (∫ x in (0:ℝ)..1, (x*(1-x^2)^(b-1))*x^2) = 1 / (2*b*(b+1)) := by
  have h₁ := weight_moment (b := b-1) (by linarith)
  have h₂ := weight_moment (b := b) (by linarith)
  have hpoint : ∀ x ∈ Icc (0:ℝ) 1,
      (x*(1-x^2)^(b-1))*x^2 = x*(1-x^2)^(b-1) - x*(1-x^2)^b := by
    intro x hx
    have hx0 : 0 ≤ 1-x^2 := by nlinarith [hx.1, hx.2]
    have he : (1-x^2)^b = (1-x^2)^(b-1)*(1-x^2) := by
      simpa [sub_add_cancel] using
        (Real.rpow_add_one' hx0 (by linarith : (b - 1) + 1 ≠ 0))
    rw [he]
    ring
  rw [intervalIntegral.integral_congr (by
      intro x hx
      exact hpoint x (by simpa only [uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] using hx)),
    intervalIntegral.integral_sub h₁.1 h₂.1, h₁.2, h₂.2]
  simp only [sub_add_cancel]
  field_simp [ne_of_gt hb, ne_of_gt (by linarith : 0 < b+1)]
  ring

private lemma radial_upper {p q α t : ℝ} (hp : 0 < p) (hpq : p < q)
    (hα : 0 < α) (ht : 0 ≤ t) :
    radialIntegral p q α t ≤ 1 + ((1+t)^(q/p)-1)/(α*q+1) := by
  have hq : 0 < q := hp.trans hpq
  have hb : 0 < α*q := mul_pos hα hq
  have hr : 1 ≤ q/p := (le_div_iff₀ hp).2 (by linarith)
  have hw := weight_moment (b := α*q-1) (by linarith)
  have hcont : ContinuousOn (fun x : ℝ => (1+t*x^2)^(q/p)) (uIcc (0:ℝ) 1) := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro x hx
    left
    positivity
  have hc : ContinuousOn (fun x : ℝ => 1+((1+t)^(q/p)-1)*x^2)
      (uIcc (0:ℝ) 1) := by fun_prop
  have hle := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (hw.1.mul_continuousOn hcont) (hw.1.mul_continuousOn hc) (fun x hx => by
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg hx.1 (Real.rpow_nonneg (by nlinarith [hx.1, hx.2]) _))
      have hx2 : 0 ≤ x^2 := sq_nonneg x
      have hx1 : x^2 ≤ 1 := by nlinarith [hx.1, hx.2]
      have hj := (convexOn_rpow hr).2 (x := (1:ℝ)) (y := 1+t)
        (by norm_num) (by simp only [mem_Ici]; linarith)
        (by linarith : 0 ≤ 1-x^2) hx2 (by ring)
      simp only [smul_eq_mul, Real.one_rpow] at hj
      have he : (1-x^2)*1+x^2*(1+t) = 1+t*x^2 := by ring
      rw [he] at hj
      nlinarith [hj])
  have hex : (∫ x in (0:ℝ)..1,
      (x*(1-x^2)^(α*q-1)) * (1+((1+t)^(q/p)-1)*x^2)) =
      1/(2*(α*q)) + ((1+t)^(q/p)-1)/(2*(α*q)*(α*q+1)) := by
    calc
      _ = (∫ x in (0:ℝ)..1, x*(1-x^2)^(α*q-1)) +
          ((1+t)^(q/p)-1) * (∫ x in (0:ℝ)..1, (x*(1-x^2)^(α*q-1))*x^2) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hw.1
          ((hw.1.mul_continuousOn (by fun_prop : ContinuousOn (fun x : ℝ => x^2)
            (uIcc (0:ℝ) 1))).const_mul _)]
        congr 1
        ext x
        ring
      _ = _ := by rw [hw.2, weight_square hb]; congr 2 <;> ring
  rw [hex] at hle
  unfold radialIntegral
  have h := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2*α*q)
  convert h using 1
  field_simp

private lemma evaluation_deriv {p q α : ℝ} (hp : 0 < p) (hα : 0 < α) :
    HasDerivAt (evaluationExcess p q α) ((q/p)/(1+α*p)) 0 := by
  have hc : 0 < 1+α*p := by positivity
  have h₁ := ((hasDerivAt_const (0:ℝ) (1:ℝ)).add
    ((hasDerivAt_id (0:ℝ)).const_mul (1/(1+α*p)))).rpow_const
      (p := 2*q/p) (Or.inl (by norm_num))
  have h₂ := ((hasDerivAt_const (0:ℝ) (1:ℝ)).sub
    ((hasDerivAt_id (0:ℝ)).const_mul ((1/(1+α*p))^2))).rpow_const
      (p := α*q+q/p) (Or.inl (by norm_num))
  convert h₁.mul h₂ using 1
  · rfl
  · dsimp
    simp only [mul_zero, add_zero, sub_zero, Real.one_rpow, zero_add, zero_sub,
      one_mul, mul_one]
    field_simp
    ring

/-- For all positive finite p < q and positive alpha, some squared family parameter
strictly separates the radial norm power from the normalized evaluation power. -/
theorem exists_gap {p q α : ℝ} (hp : 0 < p) (hpq : p < q) (hα : 0 < α) :
    ∃ t, 0 < t ∧ t < 1 ∧ radialIntegral p q α t < evaluationExcess p q α t := by
  let U : ℝ → ℝ := fun t => 1+((1+t)^(q/p)-1)/(α*q+1)
  have hq : 0 < q := hp.trans hpq
  have hc : 0 < 1+α*p := by positivity
  have hd : 1+α*p < α*q+1 := by nlinarith
  have hU : HasDerivAt U ((q/p)/(α*q+1)) 0 := by
    have h := (((hasDerivAt_id (0:ℝ)).const_add 1).rpow_const
      (p := q/p) (Or.inl (by norm_num))).sub_const 1
    simpa [U] using (h.div_const (α*q+1)).const_add 1
  have hE := evaluation_deriv (q := q) hp hα
  have hD : 0 < (q/p)/(1+α*p) - (q/p)/(α*q+1) :=
    sub_pos.mpr (div_lt_div_of_pos_left (div_pos hq hp) hc hd)
  have hpos := (hE.sub hU).tendsto_slope_zero_right.eventually (eventually_gt_nhds hD)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] (0:ℝ), t < 1 :=
    (eventually_lt_nhds (zero_lt_one : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htpos, htone, ht⟩ := (hpos.and (hsmall.and self_mem_nhdsWithin)).exists
  refine ⟨t, ht, htone, (radial_upper hp hpq hα ht.le).trans_lt ?_⟩
  have hz : evaluationExcess p q α 0 - U 0 = 0 := by
    simp [evaluationExcess, U]
  simp only [zero_add, Pi.sub_apply, smul_eq_mul, hz, sub_zero] at htpos
  have hi : 0 < t⁻¹ := inv_pos.mpr ht
  dsimp [U] at *
  nlinarith

end D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap
