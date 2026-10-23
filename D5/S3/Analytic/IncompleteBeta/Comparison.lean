/- GID: D5/S3/Analytic/IncompleteBeta/Comparison
   generality: G
   mirror-B: D5/B/S3/Analytic/IncompleteBeta/Comparison
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp]
   utility: none
   digest: Strict comparison of symmetric beta means under increasing shape imbalance. -/

import D5.S3.Analytic.KilbasSaigo.Bounds
import D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Symmetric beta densities become ordered cosh tilts after reflection. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Set MeasureTheory
open scoped Real

namespace D5.S3.Analytic.IncompleteBeta.Comparison

/-- The normalized beta mean at shape parameters `m+d` and `m-d`. -/
def betaMean (W : ℝ → ℝ) (m d : ℝ) : ℝ :=
  (Real.Gamma (m + d) * Real.Gamma (m - d) / Real.Gamma (2 * m))⁻¹ *
    ∫ u in (0 : ℝ)..1, u ^ (m + d - 1) * (1 - u) ^ (m - d - 1) * W u

private def folded (m d u : ℝ) : ℝ :=
  D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight
      (1 - m + d) (2 * m - 1) u +
    D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight
      (1 - m + d) (2 * m - 1) (1 - u)

private lemma cosh_ratio_strictMono {d e : ℝ} (hd : 0 ≤ d) (hde : d < e) :
    StrictMonoOn (fun v : ℝ => Real.cosh (e * v) / Real.cosh (d * v)) (Ioi 0) := by
  have hc : Continuous (fun v : ℝ => Real.cosh (e*v) / Real.cosh (d*v)) := by
    exact (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).div
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
      (fun v => (Real.cosh_pos _).ne')
  apply strictMonoOn_of_deriv_pos (convex_Ioi _) hc.continuousOn
  intro v hv
  have hv' : 0 < v := interior_subset hv
  have he : 0 < e := lt_of_le_of_lt hd hde
  have H := (((hasDerivAt_id v).const_mul e).cosh).div
    (((hasDerivAt_id v).const_mul d).cosh) (Real.cosh_pos _).ne'
  have H' : HasDerivAt (fun v : ℝ => Real.cosh (e*v) / Real.cosh (d*v))
      ((Real.sinh (e*v) * e * Real.cosh (d*v) -
        Real.cosh (e*v) * (Real.sinh (d*v) * d)) / Real.cosh (d*v)^2) v := by
    convert H using 1 <;> simp only [id_eq, mul_one]
    funext x
    rfl
  rw [H'.deriv]
  apply div_pos _ (sq_pos_of_pos (Real.cosh_pos _))
  rcases hd.eq_or_lt with rfl | hd'
  · simpa using mul_pos (Real.sinh_pos_iff.mpr (mul_pos he hv')) he
  · have hg := D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.g_strictMonoOn
      hv' hd' he hde
    unfold D5.S3.Entropy.RenyiCombining.ArimotoHyperbolic.g at hg
    have hcross := (div_lt_div_iff₀ (Real.cosh_pos (d*v))
      (Real.cosh_pos (e*v))).mp hg
    nlinarith

private lemma folded_eq {m d u : ℝ} (hu : u ∈ Ioo 0 1) :
    folded m d u = 2 * (u * (1 - u)) ^ (m - 1) *
      Real.cosh (d * Real.log ((1 - u) / u)) := by
  have h1 : 0 < 1 - u := sub_pos.mpr hu.2
  dsimp only [folded, D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight]
  rw [show 2 * m - 1 + (1 - m + d) - 1 = m + d - 1 by ring,
    show -(1 - m + d) = m - d - 1 by ring]
  simp only [sub_sub_cancel]
  rw [Real.mul_rpow hu.1.le h1.le, Real.cosh_eq]
  simp only [Real.rpow_def_of_pos hu.1, Real.rpow_def_of_pos h1,
    Real.log_div h1.ne' hu.1.ne']
  have hA : Real.log u * (m + d - 1) + Real.log (1-u) * (m-d-1) =
      Real.log u * (m-1) + Real.log (1-u) * (m-1) -
        d * (Real.log (1-u) - Real.log u) := by ring
  have hB : Real.log (1-u) * (m+d-1) + Real.log u * (m-d-1) =
      Real.log u * (m-1) + Real.log (1-u) * (m-1) +
        d * (Real.log (1-u) - Real.log u) := by ring
  rw [← Real.exp_add, ← Real.exp_add, hA, hB]
  simp only [Real.exp_sub, Real.exp_add, Real.exp_neg]
  ring

private lemma folded_pos {m d u : ℝ} (hu : u ∈ Ioo 0 1) : 0 < folded m d u := by
  rw [folded_eq hu]
  exact mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos
    (mul_pos hu.1 (sub_pos.mpr hu.2)) _)) (Real.cosh_pos _)

private lemma folded_ratio_strictAnti {m d e : ℝ} (hd : 0 ≤ d) (hde : d < e) :
    StrictAntiOn (fun u => folded m e u / folded m d u) (Ioo 0 (1/2)) := by
  intro u hu v hv huv
  have hu1 : u ∈ Ioo 0 1 := ⟨hu.1, by linarith [hu.2]⟩
  have hv1 : v ∈ Ioo 0 1 := ⟨hv.1, by linarith [hv.2]⟩
  have hvlog : 0 < Real.log ((1-v)/v) := Real.log_pos (by
    apply (one_lt_div hv.1).mpr
    linarith [hv.2])
  have hulog : 0 < Real.log ((1-u)/u) := Real.log_pos (by
    apply (one_lt_div hu.1).mpr
    linarith [hu.2])
  have hlog : Real.log ((1-v)/v) < Real.log ((1-u)/u) := by
    apply Real.log_lt_log (div_pos (by linarith [hv.2]) hv.1)
    apply (div_lt_div_iff₀ hv.1 hu.1).mpr
    nlinarith
  have H := cosh_ratio_strictMono hd hde hvlog hulog hlog
  dsimp only
  rw [folded_eq hu1, folded_eq hu1, folded_eq hv1, folded_eq hv1]
  have hpu : 2 * (u * (1-u)) ^ (m-1) ≠ 0 :=
    (mul_pos (by norm_num : (0:ℝ)<2)
      (Real.rpow_pos_of_pos (mul_pos hu.1 (sub_pos.mpr hu1.2)) _)).ne'
  have hpv : 2 * (v * (1-v)) ^ (m-1) ≠ 0 :=
    (mul_pos (by norm_num : (0:ℝ)<2)
      (Real.rpow_pos_of_pos (mul_pos hv.1 (sub_pos.mpr hv1.2)) _)).ne'
  simpa only [mul_div_mul_left _ _ hpu, mul_div_mul_left _ _ hpv] using H

private lemma weighted_means_lt {p q W : ℝ → ℝ} {h : ℝ} (hh : 0 < h)
    (hp : IntervalIntegrable p volume 0 h) (hq : IntervalIntegrable q volume 0 h)
    (hpW : IntervalIntegrable (fun u => p u * W u) volume 0 h)
    (hqW : IntervalIntegrable (fun u => q u * W u) volume 0 h)
    (hp0 : ∀ u ∈ Ioo 0 h, 0 < p u) (hq0 : ∀ u ∈ Ioo 0 h, 0 < q u)
    (hW : StrictMonoOn W (Ioo 0 h))
    (hR : StrictAntiOn (fun u => q u / p u) (Ioo 0 h)) :
    (∫ u in (0:ℝ)..h, q u * W u) / (∫ u in (0:ℝ)..h, q u) <
      (∫ u in (0:ℝ)..h, p u * W u) / (∫ u in (0:ℝ)..h, p u) := by
  let P := ∫ u in (0:ℝ)..h, p u
  let Q := ∫ u in (0:ℝ)..h, q u
  let A := ∫ u in (0:ℝ)..h, p u * W u
  let B := ∫ u in (0:ℝ)..h, q u * W u
  let E := fun x => (q x * A - (W x * q x) * P) -
    (p x * B - (W x * p x) * Q)
  have hP : 0 < P := intervalIntegral.intervalIntegral_pos_of_pos_on hp hp0 hh
  have hQ : 0 < Q := intervalIntegral.intervalIntegral_pos_of_pos_on hq hq0 hh
  have hEint : IntervalIntegrable E volume 0 h := by
    dsimp only [E]
    simpa only [mul_comm (W _) (q _), mul_comm (W _) (p _)] using
      ((hq.mul_const A).sub (hqW.mul_const P)).sub
        ((hp.mul_const B).sub (hpW.mul_const Q))
  have hEpos (x : ℝ) (hx : x ∈ Ioo 0 h) : 0 < E x := by
    let K := fun y => (W y - W x) * (p y * q x - q y * p x)
    have hKexp : K = fun y =>
        (q x * (p y * W y) - (W x * q x) * p y) -
          (p x * (q y * W y) - (W x * p x) * q y) := by
      funext y
      dsimp [K]
      ring
    have hKint : IntervalIntegrable K volume 0 h := by
      rw [hKexp]
      exact ((hpW.const_mul _).sub (hp.const_mul _)).sub
        ((hqW.const_mul _).sub (hq.const_mul _))
    have hKpos (y : ℝ) (hy : y ∈ Ioo 0 h) (hyx : y ≠ x) : 0 < K y := by
      rcases lt_or_gt_of_ne hyx with hyx | hxy
      · have hdet : p y * q x - q y * p x < 0 := by
          have H := (div_lt_div_iff₀ (hp0 x hx) (hp0 y hy)).mp (hR hy hx hyx)
          nlinarith
        exact mul_pos_of_neg_of_neg (sub_neg.mpr (hW hy hx hyx)) hdet
      · have hdet : 0 < p y * q x - q y * p x := by
          have H := (div_lt_div_iff₀ (hp0 y hy) (hp0 x hx)).mp (hR hx hy hxy)
          nlinarith
        exact mul_pos (sub_pos.mpr (hW hx hy hxy)) hdet
    have hKnonneg : ∀ y ∈ Ioo 0 h, 0 ≤ K y := by
      intro y hy
      by_cases he : y = x
      · simp [K, he]
      · exact (hKpos y hy he).le
    have hKae : 0 ≤ᵐ[volume.restrict (Set.uIoc 0 h)] K := by
      rw [Set.uIoc_of_le hh.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      exact (ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall hKnonneg)
    have hsupport : Ioo 0 x ⊆ Function.support K ∩ Ioc 0 h := by
      intro y hy
      have hyh : y ∈ Ioo 0 h := ⟨hy.1, hy.2.trans hx.2⟩
      exact ⟨(hKpos y hyh hy.2.ne).ne', ⟨hy.1, hyh.2.le⟩⟩
    have hKI : 0 < ∫ y in (0:ℝ)..h, K y :=
      (intervalIntegral.integral_pos_iff_support_of_nonneg_ae' hKae hKint).mpr
        ⟨hh, ((Measure.measure_Ioo_pos volume).mpr hx.1).trans_le (measure_mono hsupport)⟩
    have heq : (∫ y in (0:ℝ)..h, K y) = E x := by
      rw [hKexp, intervalIntegral.integral_sub
        ((hpW.const_mul _).sub (hp.const_mul _))
        ((hqW.const_mul _).sub (hq.const_mul _)),
        intervalIntegral.integral_sub (hpW.const_mul _) (hp.const_mul _),
        intervalIntegral.integral_sub (hqW.const_mul _) (hq.const_mul _)]
      simp only [intervalIntegral.integral_const_mul]
      rfl
    exact heq ▸ hKI
  have hEI := intervalIntegral.intervalIntegral_pos_of_pos_on hEint hEpos hh
  have hEIeq : (∫ x in (0:ℝ)..h, E x) = 2 * (Q * A - P * B) := by
    dsimp only [E]
    simp_rw [mul_comm (W _) (q _), mul_comm (W _) (p _)]
    rw [intervalIntegral.integral_sub
      ((hq.mul_const A).sub (hqW.mul_const P))
      ((hp.mul_const B).sub (hpW.mul_const Q)),
      intervalIntegral.integral_sub (hq.mul_const _) (hqW.mul_const _),
      intervalIntegral.integral_sub (hp.mul_const _) (hpW.mul_const _)]
    simp only [intervalIntegral.integral_mul_const]
    dsimp [P, Q, A, B]
    ring
  change B / Q < A / P
  apply (div_lt_div_iff₀ hQ hP).mpr
  rw [hEIeq] at hEI
  nlinarith

private lemma fold_integral {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1) :
    (∫ u in (0:ℝ)..1, f u) =
      ∫ u in (0:ℝ)..(1/2), f u + f (1-u) := by
  have hleft : IntervalIntegrable f volume 0 (1/2) :=
    hf.mono_set (by norm_num [Set.uIcc_of_le]; intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hright : IntervalIntegrable f volume (1/2) 1 :=
    hf.mono_set (by norm_num [Set.uIcc_of_le]; intro x hx; constructor <;> linarith [hx.1, hx.2])
  have href : IntervalIntegrable (fun u => f (1-u)) volume 0 (1/2) := by
    convert (hright.comp_sub_left 1).symm using 1 <;> norm_num
  rw [intervalIntegral.integral_add hleft href,
    intervalIntegral.integral_comp_sub_left]
  norm_num only [sub_zero, show (1:ℝ)-1/2=1/2 by norm_num]
  exact (intervalIntegral.integral_add_adjacent_intervals hleft hright).symm

private lemma folded_integrable {m d : ℝ} (hp : 0 < m+d) (hq : 0 < m-d) :
    IntervalIntegrable (folded m d) volume 0 (1/2) := by
  have hi := D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight_integrable
    (α := 1 - m + d) (a := 2 * m - 1) (by linarith) (by linarith)
  have hr : IntervalIntegrable
      (fun u => D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight
        (1 - m + d) (2 * m - 1) (1 - u)) volume 0 1 := by
    convert (hi.comp_sub_left 1).symm using 1 <;> norm_num
  exact (hi.add hr).mono_set (by
    norm_num [Set.uIcc_of_le]
    intro x hx
    constructor <;> linarith [hx.1, hx.2])

private lemma betaMean_eq_foldedMean {W : ℝ → ℝ}
    (hW : ContinuousOn W (Icc 0 1))
    (hsymm : ∀ u ∈ Icc 0 1, W (1-u) = W u)
    {m d : ℝ} (hp : 0 < m+d) (hq : 0 < m-d) :
    betaMean W m d =
      (∫ u in (0:ℝ)..(1/2), folded m d u * W u) /
        (∫ u in (0:ℝ)..(1/2), folded m d u) := by
  have hi := D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight_integrable
    (α := 1 - m + d) (a := 2 * m - 1) (by linarith) (by linarith)
  have hWi := hi.mul_continuousOn (by simpa only [Set.uIcc_of_le zero_le_one] using hW)
  have hnum : (∫ u in (0:ℝ)..1,
      D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight
        (1 - m + d) (2 * m - 1) u * W u) =
      ∫ u in (0:ℝ)..(1/2), folded m d u * W u := by
    rw [fold_integral hWi]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro u hu
    dsimp only
    rw [hsymm u ⟨hu.1.le, by linarith [hu.2]⟩]
    dsimp [folded]
    ring
  have hden : (∫ u in (0:ℝ)..(1/2), folded m d u) =
      Real.Gamma (m+d) * Real.Gamma (m-d) / Real.Gamma (2*m) := by
    change (∫ u in (0:ℝ)..(1/2),
      D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight
          (1 - m + d) (2 * m - 1) u +
        D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight
          (1 - m + d) (2 * m - 1) (1 - u)) = _
    rw [← fold_integral hi]
    simpa only [show 2 * m - 1 + (1 - m + d) = m + d by ring,
      show 1 - (1 - m + d) = m - d by ring,
      show 2 * m - 1 + 1 = 2 * m by ring] using
      D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.integral_weight
        (α := 1 - m + d) (a := 2 * m - 1) (by linarith) (by linarith)
  unfold betaMean
  have hw : (fun u : ℝ => u ^ (m + d - 1) * (1 - u) ^ (m - d - 1)) =
      D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight
        (1 - m + d) (2 * m - 1) := by
    funext u
    unfold D5.S3.Analytic.KilbasSaigo.Bounds.FractionalCertificate.weight
    congr 2 <;> ring
  simp_rw [← hw] at hnum
  rw [hnum, hden]
  ring

/-- A symmetric continuous function increasing toward the midpoint has strictly
smaller beta mean when the positive shape parameters have larger imbalance. -/
theorem betaMean_strictAntiOn {W : ℝ → ℝ}
    (hW : ContinuousOn W (Icc 0 1))
    (hsymm : ∀ u ∈ Icc 0 1, W (1-u) = W u)
    (hmono : StrictMonoOn W (Ioc 0 (1/2))) {m : ℝ} (hm : 0 < m) :
    StrictAntiOn (betaMean W m) (Ico 0 m) := by
  intro d hd e he hde
  have hdp : 0 < m+d := by linarith [hd.1]
  have hdq : 0 < m-d := sub_pos.mpr hd.2
  have hep : 0 < m+e := by linarith [he.1]
  have heq : 0 < m-e := sub_pos.mpr he.2
  rw [betaMean_eq_foldedMean hW hsymm hep heq,
    betaMean_eq_foldedMean hW hsymm hdp hdq]
  have hW' : ContinuousOn W (Set.uIcc (0:ℝ) (1/2)) := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1/2)]
    exact hW.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  exact weighted_means_lt (by norm_num) (folded_integrable hdp hdq)
    (folded_integrable hep heq) ((folded_integrable hdp hdq).mul_continuousOn hW')
    ((folded_integrable hep heq).mul_continuousOn hW')
    (fun u hu => folded_pos ⟨hu.1, by linarith [hu.2]⟩)
    (fun u hu => folded_pos ⟨hu.1, by linarith [hu.2]⟩)
    (hmono.mono Ioo_subset_Ioc_self) (folded_ratio_strictAnti hd.1 hde)

end D5.S3.Analytic.IncompleteBeta.Comparison
