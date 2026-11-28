/- GID: D5/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuQubitSharpTwoExactAffinity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp scalar affinity stability for Wu's normalized one-mode two-deficit on the closed qubit spectrum. -/

import D5.S3.Quantum.Semigroups.WuQubitSharpTwoRigidity
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact affinity stability for Wu's normalized qubit deficit

At exponent two, the radial integral and the angular square give the sharp
coefficient for the squared affinity defect. The bound holds on the closed
spectrum and the quotient approaches the coefficient along faithful spectra.
-/

noncomputable section

open Set

namespace D5.S3.Quantum.Semigroups.WuQubitSharpTwoRigidity

set_option autoImplicit false

section ExactAffinity

open Filter MeasureTheory
open scoped Topology Interval
open D5.S3.QuantumChannels.ContractionSpectrumOrder (hasDerivAt_artanh)

private theorem tanh_nonneg {h : ℝ} (hh : 0 ≤ h) : 0 ≤ Real.tanh h := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr hh) (Real.cosh_pos h).le

private theorem tanh_pos {h : ℝ} (hh : 0 < h) : 0 < Real.tanh h := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (Real.sinh_pos_iff.mpr hh) (Real.cosh_pos h)

private def affinityDen (w x : ℝ) : ℝ := 1 - w * x ^ 2

private def affinityKernel (u w x : ℝ) : ℝ :=
  (1 - x ^ 2) / (affinityDen u x * affinityDen w x)

private def affinitySecant (u w : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, affinityKernel u w x

/-- The integral J in the exact one-mode coefficient. -/
def affinityJ (u : ℝ) : ℝ := affinitySecant u u

theorem affinityJ_eq_integral (u : ℝ) :
    affinityJ u = ∫ x in (0 : ℝ)..1, (1 - x ^ 2) / (1 - u * x ^ 2) ^ 2 := by
  unfold affinityJ affinitySecant affinityKernel affinityDen
  simp only [pow_two]

private def affinityF (w : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, (1 - w) / affinityDen w x

private theorem affinity_unit_sq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : x ^ 2 ≤ 1 := by
  simpa using pow_le_pow_left₀ hx.1 hx.2 2

private theorem affinityDen_pos {w x : ℝ} (hw : w ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ Icc (0 : ℝ) 1) : 0 < affinityDen w x := by
  have hm := mul_le_mul_of_nonneg_left (affinity_unit_sq hx) hw.1
  dsimp [affinityDen]
  linarith only [hm, hw.2]

private theorem continuousOn_affinityKernel {u w : ℝ}
    (hu : u ∈ Ico (0 : ℝ) 1) (hw : w ∈ Ico (0 : ℝ) 1) :
    ContinuousOn (affinityKernel u w) (Icc 0 1) := by
  unfold affinityKernel
  exact (show Continuous (fun x : ℝ => 1 - x ^ 2) by fun_prop).continuousOn.div
    (show Continuous (fun x : ℝ => affinityDen u x * affinityDen w x) by
      unfold affinityDen
      fun_prop).continuousOn
    (fun x hx => (mul_pos (affinityDen_pos hu hx) (affinityDen_pos hw hx)).ne')

theorem affinityJ_pos {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) : 0 < affinityJ u := by
  unfold affinityJ affinitySecant
  refine intervalIntegral.integral_pos zero_lt_one (continuousOn_affinityKernel hu hu) ?_ ?_
  · intro x hx
    have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    exact div_nonneg (sub_nonneg.mpr (affinity_unit_sq hx'))
      (mul_pos (affinityDen_pos hu hx') (affinityDen_pos hu hx')).le
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, by norm_num [affinityKernel, affinityDen]⟩

theorem affinityJ_zero : affinityJ 0 = 2 / 3 := by
  change (∫ x in (0 : ℝ)..1, affinityKernel 0 0 x) = _
  simp only [affinityKernel, affinityDen, zero_mul, sub_zero, mul_one, div_one]
  have hc : Continuous (fun x : ℝ => x ^ 2) := by fun_prop
  rw [intervalIntegral.integral_sub
    (continuous_const.intervalIntegrable 0 1) (hc.intervalIntegrable 0 1),
    intervalIntegral.integral_const, integral_pow]
  norm_num

private theorem affinityF_zero : affinityF 0 = 1 := by
  norm_num [affinityF, affinityDen, intervalIntegral.integral_const]

private theorem affinityF_sq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    affinityF (t ^ 2) = (1 - t ^ 2) * Real.artanh t / t := by
  have hsub : ∀ x ∈ uIcc (0 : ℝ) t, x ∈ Ioo (-1 : ℝ) 1 := by
    intro x hx
    rw [uIcc_of_le ht.1.le] at hx
    exact ⟨by linarith only [hx.1], hx.2.trans_lt ht.2⟩
  have hc : ContinuousOn (fun x : ℝ => 1 / (1 - x ^ 2)) (uIcc 0 t) :=
    continuousOn_const.div
      (show Continuous (fun x : ℝ => 1 - x ^ 2) by fun_prop).continuousOn
      (fun x hx => by
        have hx' := hsub x hx
        rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring]
        exact (mul_pos (sub_pos.mpr hx'.2) (show 0 < 1 + x by linarith only [hx'.1])).ne')
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_artanh (hsub x hx)) hc.intervalIntegrable
  rw [Real.artanh_zero, sub_zero] at hf
  calc
    affinityF (t ^ 2) =
        (1 - t ^ 2) * (∫ x in (0 : ℝ)..1, 1 / (1 - (t * x) ^ 2)) := by
      rw [affinityF, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x _
      change (1 - t ^ 2) / affinityDen (t ^ 2) x =
        (1 - t ^ 2) * (1 / (1 - (t * x) ^ 2))
      simp [affinityDen, mul_pow, div_eq_mul_inv]
    _ = (1 - t ^ 2) * Real.artanh t / t := by
      rw [intervalIntegral.integral_comp_mul_left
        (fun x : ℝ => 1 / (1 - x ^ 2)) ht.1.ne']
      simp only [mul_zero, mul_one, smul_eq_mul, hf]
      ring

private theorem affinityF_sub {u w : ℝ} (hu : u ∈ Ico (0 : ℝ) 1)
    (hw : w ∈ Ico (0 : ℝ) 1) :
    affinityF u - affinityF w = (w - u) * affinitySecant u w := by
  have hcont (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1) :
      ContinuousOn (fun x : ℝ => (1 - r) / affinityDen r x) (Icc 0 1) :=
    continuousOn_const.div
      (show Continuous (affinityDen r) by unfold affinityDen; fun_prop).continuousOn
      (fun x hx => (affinityDen_pos hr hx).ne')
  rw [affinityF, affinityF, affinitySecant, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub
      ((hcont u hu).intervalIntegrable_of_Icc zero_le_one)
      ((hcont w hw).intervalIntegrable_of_Icc zero_le_one)]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le zero_le_one] at hx
  unfold affinityKernel
  field_simp [(affinityDen_pos hu hx).ne', (affinityDen_pos hw hx).ne']
  unfold affinityDen
  ring

private theorem affinityJ_le_secant {u w : ℝ} (hu : u ∈ Ico (0 : ℝ) 1)
    (hw : w ∈ Ico (0 : ℝ) 1) (huw : u ≤ w) : affinityJ u ≤ affinitySecant u w := by
  unfold affinityJ affinitySecant
  refine intervalIntegral.integral_mono_on zero_le_one
    ((continuousOn_affinityKernel hu hu).intervalIntegrable_of_Icc zero_le_one)
    ((continuousOn_affinityKernel hu hw).intervalIntegrable_of_Icc zero_le_one) ?_
  intro x hx
  have hden : affinityDen w x ≤ affinityDen u x :=
    sub_le_sub_left (mul_le_mul_of_nonneg_right huw (sq_nonneg x)) _
  exact div_le_div_of_nonneg_left (sub_nonneg.mpr (affinity_unit_sq hx))
    (mul_pos (affinityDen_pos hu hx) (affinityDen_pos hw hx))
    (mul_le_mul_of_nonneg_left hden (affinityDen_pos hu hx).le)

private theorem affinitySecant_le {u w : ℝ} (hu : u ∈ Ico (0 : ℝ) 1)
    (hw : w ∈ Ico (0 : ℝ) 1) (huw : u ≤ w) :
    affinitySecant u w ≤ (1 - u) / (1 - w) * affinityJ u := by
  let c := (1 - u) / (1 - w)
  change affinitySecant u w ≤ c * affinitySecant u u
  rw [affinitySecant, affinitySecant, ← intervalIntegral.integral_const_mul]
  have hcu : ContinuousOn (fun x => c * affinityKernel u u x) (Icc 0 1) :=
    continuousOn_const.mul (continuousOn_affinityKernel hu hu)
  refine intervalIntegral.integral_mono_on zero_le_one
    ((continuousOn_affinityKernel hu hw).intervalIntegrable_of_Icc zero_le_one)
    (hcu.intervalIntegrable_of_Icc zero_le_one) ?_
  intro x hx
  have hden : affinityDen u x ≤ c * affinityDen w x := by
    dsimp [c]
    rw [div_mul_eq_mul_div₀]
    apply (le_div_iff₀ (sub_pos.mpr hw.2)).mpr
    have hp := mul_nonneg (sub_nonneg.mpr huw) (sub_nonneg.mpr (affinity_unit_sq hx))
    unfold affinityDen
    nlinarith only [hp]
  have hdu := affinityDen_pos hu hx
  have hdw := affinityDen_pos hw hx
  unfold affinityKernel
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (mul_pos hdu hdw) (mul_pos hdu hdu)).mpr
  have hm := mul_le_mul_of_nonneg_left hden
    (mul_nonneg (sub_nonneg.mpr (affinity_unit_sq hx)) hdu.le)
  convert hm using 1 <;> ring

private theorem affinitySecant_tendsto {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    Tendsto (affinitySecant u) (𝓝[>] u) (𝓝 (affinityJ u)) := by
  have hc : ContinuousAt (fun w : ℝ => (1 - u) / (1 - w) * affinityJ u) u :=
    (continuousAt_const.div (continuousAt_const.sub continuousAt_id)
      (sub_pos.mpr hu.2).ne').mul continuousAt_const
  have hup : Tendsto (fun w : ℝ => (1 - u) / (1 - w) * affinityJ u) (𝓝[>] u)
      (𝓝 (affinityJ u)) := by
    simpa only [div_self (sub_pos.mpr hu.2).ne', one_mul] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT hu.2] with w hw
    exact affinityJ_le_secant hu ⟨hu.1.trans hw.1.le, hw.2⟩ hw.1.le
  · filter_upwards [Ioo_mem_nhdsGT hu.2] with w hw
    exact affinitySecant_le hu ⟨hu.1.trans hw.1.le, hw.2⟩ hw.1.le

/-- Convert square-root polarization to spectral polarization. -/
def polarizationOfHalf (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

private theorem polarizationOfHalf_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    polarizationOfHalf t ∈ Icc (0 : ℝ) 1 := by
  unfold polarizationOfHalf
  exact ⟨div_nonneg (mul_nonneg (by norm_num) ht.1) (by positivity),
    (div_le_one₀ (by positivity)).mpr (by nlinarith only [sq_nonneg (1 - t)])⟩

private theorem exactAffinity_half_polarization {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    let t := v / (1 + spectralRoot v)
    t ∈ Icc (0 : ℝ) 1 ∧ polarizationOfHalf t = v ∧
      1 + spectralRoot v = 2 / (1 + t ^ 2) := by
  let s := spectralRoot v
  let t := v / (1 + s)
  change t ∈ Icc (0 : ℝ) 1 ∧ polarizationOfHalf t = v ∧ 1 + s = 2 / (1 + t ^ 2)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs1 : 0 < 1 + s := by positivity
  have ht : t ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hv.1 hs1.le, (div_le_one₀ hs1).mpr (by linarith only [hv.2, hs])⟩
  have htsq : t ^ 2 * (1 + s) = 1 - s := by
    calc
      t ^ 2 * (1 + s) = v ^ 2 / (1 + s) := by dsimp [t]; field_simp [hs1.ne'] <;> ring
      _ = 1 - s := by
        have hrad : 0 ≤ 1 - v ^ 2 :=
          sub_nonneg.mpr ((sq_le_one_iff₀ hv.1).mpr hv.2)
        have hssq : s ^ 2 = 1 - v ^ 2 := Real.sq_sqrt hrad
        apply (div_eq_iff hs1.ne').mpr
        nlinarith only [hssq]
  have htplus : (1 + t ^ 2) * (1 + s) = 2 := by nlinarith only [htsq]
  have htmul : t * (1 + s) = v := div_mul_cancel₀ _ hs1.ne'
  have ht1 : 0 < 1 + t ^ 2 := by positivity
  refine ⟨ht, (div_eq_iff ht1.ne').mpr ?_, (eq_div_iff ht1.ne').mpr ?_⟩
  · calc
      2 * t = ((1 + t ^ 2) * (1 + s)) * t := by rw [htplus]
      _ = (t * (1 + s)) * (1 + t ^ 2) := by ring
      _ = v * (1 + t ^ 2) := by rw [htmul]
  · simpa only [mul_comm] using htplus

private theorem exactAffinity_bias_eq_tanh_half (h : ℝ) :
    thermalBias h = Real.tanh (h / 2) := by
  have hc : 1 + Real.cosh (2 * (h / 2)) = 2 * Real.cosh (h / 2) ^ 2 := by
    rw [Real.cosh_two_mul]
    nlinarith only [Real.cosh_sq_sub_sinh_sq (h / 2)]
  calc
    thermalBias h = Real.sinh (2 * (h / 2)) / (1 + Real.cosh (2 * (h / 2))) := by
      rw [show 2 * (h / 2) = h by ring, thermalBias]
    _ = Real.tanh (h / 2) := by
      rw [hc, Real.sinh_two_mul, Real.tanh_eq_sinh_div_cosh]
      field_simp [(Real.cosh_pos (h / 2)).ne'] <;> ring

private theorem exactAffinity_bias_mem {h : ℝ} (hh : 0 ≤ h) :
    thermalBias h ∈ Ico (0 : ℝ) 1 := by
  rw [exactAffinity_bias_eq_tanh_half]
  exact ⟨tanh_nonneg (by positivity), Real.tanh_lt_one _⟩

private theorem exactAffinity_bias_sq_mem {h : ℝ} (hh : 0 ≤ h) :
    thermalBias h ^ 2 ∈ Ico (0 : ℝ) 1 := by
  rw [exactAffinity_bias_eq_tanh_half]
  exact ⟨sq_nonneg _, Real.tanh_sq_lt_one _⟩

private theorem polarizationOfHalf_bias {h : ℝ} (hh : 0 ≤ h) :
    polarizationOfHalf (thermalBias h) = Real.tanh h := by
  have hv : Real.tanh h ∈ Icc (0 : ℝ) 1 :=
    ⟨tanh_nonneg hh, (Real.tanh_lt_one h).le⟩
  obtain ⟨_, hp, _⟩ := exactAffinity_half_polarization hv
  have hb : Real.tanh h / (1 + spectralRoot (Real.tanh h)) = thermalBias h := by
    rw [spectralRoot_tanh, Real.tanh_eq_sinh_div_cosh, thermalBias]
    have hc := (Real.cosh_pos h).ne'
    rw [show 1 + 1 / Real.cosh h = (Real.cosh h + 1) / Real.cosh h by
      rw [add_div, div_self hc], div_div_div_cancel_right₀ hc, add_comm (Real.cosh h)]
  simpa only [hb] using hp

private theorem exactAffinity_sharpCoefficient_pos {h : ℝ} (hh : 0 ≤ h) :
    0 < sharpCoefficient h := by
  rcases eq_or_lt_of_le hh with rfl | hh'
  · norm_num [sharpCoefficient]
  · rw [sharpCoefficient, if_neg hh'.ne', exactAffinity_bias_eq_tanh_half]
    exact div_pos (tanh_pos (by positivity)) hh'

private theorem sharpCoefficient_mul_affinityF {h : ℝ} (hh : 0 ≤ h) :
    sharpCoefficient h * affinityF (thermalBias h ^ 2) = 1 / (1 + Real.cosh h) := by
  rcases eq_or_lt_of_le hh with rfl | hh'
  · norm_num [sharpCoefficient, thermalBias, affinityF_zero]
  · have hk : 0 < thermalBias h := by
      rw [exactAffinity_bias_eq_tanh_half]
      exact tanh_pos (by positivity)
    have hs : 1 - thermalBias h ^ 2 = 2 / (1 + Real.cosh h) := by
      rw [thermalBias, div_pow, Real.sinh_sq]
      field_simp [show 1 + Real.cosh h ≠ 0 by positivity] <;> ring
    have hart : Real.artanh (thermalBias h) = h / 2 := by
      rw [exactAffinity_bias_eq_tanh_half, Real.artanh_tanh]
    rw [affinityF_sq ⟨hk, (exactAffinity_bias_mem hh).2⟩, hs, hart]
    calc
      _ = (sharpCoefficient h * h / thermalBias h) / (1 + Real.cosh h) := by ring
      _ = _ := by rw [sharpCoefficient_mul, div_self hk.ne']

/-- The radial remainder as a function of squared square-root polarization. -/
def radialDeficitOfSquare (h w : ℝ) : ℝ :=
  radialDeficit h (polarizationOfHalf (Real.sqrt w))

private theorem continuous_radialDeficitOfSquare (h : ℝ) : Continuous (radialDeficitOfSquare h) :=
  (continuous_radialDeficit h).comp
    (((show Continuous (fun t : ℝ => 2 * t) by fun_prop).div
      (show Continuous (fun t : ℝ => 1 + t ^ 2) by fun_prop) (fun _ => by positivity)).comp
      Real.continuous_sqrt)

private theorem radialDeficitOfSquare_bias {h : ℝ} (hh : 0 ≤ h) :
    radialDeficitOfSquare h (thermalBias h ^ 2) = 0 := by
  rw [radialDeficitOfSquare, Real.sqrt_sq (exactAffinity_bias_mem hh).1,
    polarizationOfHalf_bias hh, radialDeficit_tanh]

private theorem radialDeficitOfSquare_hasDerivAt {h w : ℝ} (hh : 0 ≤ h)
    (hw : w ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (radialDeficitOfSquare h)
      (2 * sharpCoefficient h * (affinityF (thermalBias h ^ 2) - affinityF w) /
        (1 + w) ^ 2) w := by
  let t := Real.sqrt w
  have ht : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.sqrt_pos_of_pos hw.1, by
      simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt hw.1.le hw.2⟩
  have htsq : t ^ 2 = w := Real.sq_sqrt hw.1.le
  have ht' : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith only [ht.1], ht.2⟩
  have hs : 0 < 1 - t ^ 2 := sub_pos.mpr ((sq_lt_one_iff₀ ht.1.le).mpr ht.2)
  have hp : 0 < 1 + t ^ 2 := by positivity
  have hmem : polarizationOfHalf t ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos (mul_pos (by norm_num) ht.1) hp,
      (div_lt_iff₀ hp).mpr (by nlinarith only [sq_pos_of_pos (sub_pos.mpr ht.2)])⟩
  have hp' : HasDerivAt polarizationOfHalf (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
    have hn : HasDerivAt (fun x : ℝ => 2 * x) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    have hd : HasDerivAt (fun x : ℝ => 1 + x ^ 2) (2 * t) t := by
      simpa using ((hasDerivAt_id t).pow 2).const_add 1
    have hdiv := hn.div hd hp.ne'
    change HasDerivAt polarizationOfHalf _ t at hdiv
    convert hdiv using 1
    change 2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2 =
      (2 * (1 + t ^ 2) - (2 * t) * (2 * t)) / (1 + t ^ 2) ^ 2
    ring
  have hsin : Real.sinh (2 * Real.artanh t) = 2 * t / (1 - t ^ 2) := by
    rw [Real.sinh_two_mul, Real.sinh_artanh ht', Real.cosh_artanh ht']
    calc
      _ = 2 * t / (Real.sqrt (1 - t ^ 2)) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hs.le]
  have hcos : Real.cosh (2 * Real.artanh t) = (1 + t ^ 2) / (1 - t ^ 2) := by
    rw [Real.cosh_two_mul, Real.sinh_artanh ht', Real.cosh_artanh ht']
    simp only [div_pow, Real.sq_sqrt hs.le]
    ring
  have hart : Real.artanh (polarizationOfHalf t) = 2 * Real.artanh t := by
    have he : Real.tanh (2 * Real.artanh t) = polarizationOfHalf t := by
      rw [Real.tanh_eq_sinh_div_cosh, hsin, hcos, polarizationOfHalf]
      field_simp [hs.ne', hp.ne'] <;> ring
    rw [← he, Real.artanh_tanh]
  have hd := ((radialDeficit_hasDerivAt h hmem).comp t hp').comp w
    (Real.hasDerivAt_sqrt hw.1.ne')
  rw [hart, hsin] at hd
  change HasDerivAt (radialDeficitOfSquare h) _ w at hd
  convert hd using 1
  change _ = ((2 * t / (1 - t ^ 2)) / (1 + Real.cosh h) -
    sharpCoefficient h * (2 * Real.artanh t)) *
    (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2) * (1 / (2 * t))
  rw [← htsq, affinityF_sq ht]
  have hc := sharpCoefficient_mul_affinityF hh
  have hscale : (2 * t / (1 - t ^ 2)) / (1 + Real.cosh h) =
      (2 * t / (1 - t ^ 2)) * (sharpCoefficient h * affinityF (thermalBias h ^ 2)) := by
    rw [hc]
    simp only [div_eq_mul_inv, one_mul]
  rw [hscale]
  field_simp [hs.ne', hp.ne', ht.1.ne'] <;> ring

private def affinityRoot (w : ℝ) : ℝ := Real.sqrt (1 + w)

/-- The radial part of the affinity defect, in squared half polarization. -/
def radialAffinityDefect (u w : ℝ) : ℝ := 1 - affinityRoot u / affinityRoot w

private theorem affinityRoot_pos {w : ℝ} (hw : 0 ≤ w) : 0 < affinityRoot w :=
  Real.sqrt_pos_of_pos (by positivity)

private theorem affinityRoot_sq {w : ℝ} (hw : 0 ≤ w) : affinityRoot w ^ 2 = 1 + w :=
  Real.sq_sqrt (by positivity)

private theorem affinityRoot_lt {u w : ℝ} (hu : 0 ≤ u) (huw : u < w) :
    affinityRoot u < affinityRoot w :=
  Real.sqrt_lt_sqrt (by positivity) (by nlinarith [huw])

private theorem affinityRoot_sq_diff {u w : ℝ} (hu : 0 ≤ u) (hw : 0 ≤ w) :
    (affinityRoot w - affinityRoot u) * (affinityRoot w + affinityRoot u) = w - u := by
  nlinarith only [affinityRoot_sq hu, affinityRoot_sq hw]

private theorem radialAffinityDefect_pos {u w : ℝ} (hu : 0 ≤ u) (huw : u < w) :
    0 < radialAffinityDefect u w :=
  sub_pos.mpr ((div_lt_one₀ (affinityRoot_pos (hu.trans huw.le))).mpr
    (affinityRoot_lt hu huw))

private theorem continuousOn_radialAffinityDefect (u : ℝ) :
    ContinuousOn (radialAffinityDefect u) (Ici 0) := by
  unfold radialAffinityDefect
  exact continuousOn_const.sub (continuousOn_const.div
    (show Continuous affinityRoot by unfold affinityRoot; fun_prop).continuousOn
    (fun w hw => (affinityRoot_pos hw).ne'))

private def radialAffinitySquareSlope (u w : ℝ) : ℝ :=
  affinityRoot u * (affinityRoot w - affinityRoot u) / (1 + w) ^ 2

private theorem radialAffinitySquare_hasDerivAt (u : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    HasDerivAt (fun x => radialAffinityDefect u x ^ 2) (radialAffinitySquareSlope u w) w := by
  have hq : 0 < affinityRoot w := affinityRoot_pos hw
  have hws : 0 < 1 + w := by positivity
  have hd : HasDerivAt affinityRoot (1 / (2 * affinityRoot w)) w :=
    ((hasDerivAt_id w).const_add 1).sqrt hws.ne'
  have he := (((hasDerivAt_const w (affinityRoot u)).div hd hq.ne').const_sub 1).pow 2
  change HasDerivAt (fun x => radialAffinityDefect u x ^ 2) _ w at he
  convert he using 1
  unfold radialAffinitySquareSlope
  rw [← affinityRoot_sq hw]
  norm_num <;> field_simp [hq.ne'] <;> ring

/-- The derivative ratio extends to the diagonal via the integral secant. -/
private def radialAffinitySlopeRatio (a u w : ℝ) : ℝ :=
  2 * a * (affinityRoot w + affinityRoot u) * affinitySecant u w / affinityRoot u

private theorem radialDeficitOfSquare_hasDerivAt_ratio {h w : ℝ} (hh : 0 ≤ h)
    (hw : w ∈ Ioo (0 : ℝ) 1) :
    let u := thermalBias h ^ 2
    HasDerivAt (radialDeficitOfSquare h)
      (radialAffinitySlopeRatio (sharpCoefficient h) u w * radialAffinitySquareSlope u w) w := by
  dsimp only
  let u := thermalBias h ^ 2
  have hu : u ∈ Ico (0 : ℝ) 1 := exactAffinity_bias_sq_mem hh
  have hw0 : 0 ≤ w := hw.1.le
  have hd := radialDeficitOfSquare_hasDerivAt hh hw
  change HasDerivAt (radialDeficitOfSquare h)
    (2 * sharpCoefficient h * (affinityF u - affinityF w) / (1 + w) ^ 2) w at hd
  rw [affinityF_sub hu ⟨hw.1.le, hw.2⟩, ← affinityRoot_sq_diff hu.1 hw.1.le] at hd
  convert hd using 1
  change radialAffinitySlopeRatio (sharpCoefficient h) u w * radialAffinitySquareSlope u w = _
  unfold radialAffinitySlopeRatio radialAffinitySquareSlope
  field_simp [(affinityRoot_pos hu.1).ne', show 1 + w ≠ 0 by positivity] <;> ring

private theorem radialAffinitySlopeRatio_gt {a u w : ℝ} (ha : 0 < a)
    (hu : u ∈ Ico (0 : ℝ) 1) (hw : w ∈ Ioo u 1) :
    4 * a * affinityJ u < radialAffinitySlopeRatio a u w := by
  have hs := affinityRoot_pos hu.1
  have hj := affinityJ_pos hu
  have hj' := affinityJ_le_secant hu ⟨hu.1.trans hw.1.le, hw.2⟩ hw.1.le
  have hq := affinityRoot_lt hu.1 hw.1
  unfold radialAffinitySlopeRatio
  apply (lt_div_iff₀ hs).mpr
  calc
    _ = (2 * a) * (affinityRoot u + affinityRoot u) * affinityJ u := by ring
    _ < (2 * a) * (affinityRoot w + affinityRoot u) * affinityJ u :=
      mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_left
          (show affinityRoot u + affinityRoot u < affinityRoot w + affinityRoot u by
            linarith only [hq]) (by positivity)) hj
    _ ≤ _ := mul_le_mul_of_nonneg_left hj' (by
      have := affinityRoot_pos (hu.1.trans hw.1.le)
      positivity)

private theorem radialAffinitySquareSlope_pos {u w : ℝ} (hu : 0 ≤ u) (huw : u < w) :
    0 < radialAffinitySquareSlope u w := by
  have hw : 0 ≤ w := hu.trans huw.le
  exact div_pos (mul_pos (affinityRoot_pos hu) (sub_pos.mpr (affinityRoot_lt hu huw)))
    (by positivity)

/-- Strict radial bound up to and including the rank-one endpoint. -/
theorem radialDeficitOfSquare_gt_exactAffinity {h w : ℝ} (hh : 0 ≤ h)
    (hw : w ∈ Ioc (thermalBias h ^ 2) 1) :
    4 * sharpCoefficient h * affinityJ (thermalBias h ^ 2) *
      radialAffinityDefect (thermalBias h ^ 2) w ^ 2 < radialDeficitOfSquare h w := by
  let u := thermalBias h ^ 2
  let a := sharpCoefficient h
  let L := 4 * a * affinityJ u
  let gap := fun w => radialDeficitOfSquare h w - L * radialAffinityDefect u w ^ 2
  have hu : u ∈ Ico (0 : ℝ) 1 := exactAffinity_bias_sq_mem hh
  have hc : ContinuousOn gap (Icc u 1) :=
    (continuous_radialDeficitOfSquare h).continuousOn.sub
      (continuousOn_const.mul (((continuousOn_radialAffinityDefect u).mono
        (fun _ hx => hu.1.trans hx.1)).pow 2))
  have hm : StrictMonoOn gap (Icc u 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) hc ?_
    intro w hw
    rw [interior_Icc] at hw
    have hwu : u < w := hw.1
    have hw0 := hu.1.trans hwu.le
    have hd := (radialDeficitOfSquare_hasDerivAt_ratio hh ⟨hu.1.trans_lt hwu, hw.2⟩).sub
      ((radialAffinitySquare_hasDerivAt u hw0).const_mul L)
    change HasDerivAt gap
      (radialAffinitySlopeRatio a u w * radialAffinitySquareSlope u w -
        L * radialAffinitySquareSlope u w) w at hd
    rw [hd.deriv, ← sub_mul]
    exact mul_pos
      (sub_pos.mpr (radialAffinitySlopeRatio_gt (exactAffinity_sharpCoefficient_pos hh) hu hw))
      (radialAffinitySquareSlope_pos hu.1 hwu)
  have hz : gap u = 0 := by
    have hq := affinityRoot_pos hu.1
    simpa [gap, u, radialAffinityDefect, hq.ne'] using radialDeficitOfSquare_bias hh
  have h := hm ⟨le_rfl, hu.2.le⟩ ⟨hw.1.le, hw.2⟩ hw.1
  rw [hz] at h
  exact sub_pos.mp h

/-- Strict radial bound in square-root polarization. -/
theorem radialDeficit_gt_exactAffinity {h t : ℝ} (hh : 0 ≤ h)
    (ht : t ∈ Ioc (thermalBias h) 1) :
    4 * sharpCoefficient h * affinityJ (thermalBias h ^ 2) *
      radialAffinityDefect (thermalBias h ^ 2) (t ^ 2) ^ 2 <
        radialDeficit h (polarizationOfHalf t) := by
  have hk := (exactAffinity_bias_mem hh).1
  have ht0 := hk.trans ht.1.le
  have hw : t ^ 2 ∈ Ioc (thermalBias h ^ 2) 1 :=
    ⟨pow_lt_pow_left₀ ht.1 hk (by decide : 2 ≠ 0), affinity_unit_sq ⟨ht0, ht.2⟩⟩
  simpa only [radialDeficitOfSquare, Real.sqrt_sq ht0] using
    radialDeficitOfSquare_gt_exactAffinity hh hw

/-- The corresponding radial constant is approached from higher polarization. -/
theorem radialDeficitOfSquare_exactAffinity_limit {h : ℝ} (hh : 0 ≤ h) :
    let u := thermalBias h ^ 2
    Tendsto (fun w => radialDeficitOfSquare h w / radialAffinityDefect u w ^ 2)
      (𝓝[>] u) (𝓝 (4 * sharpCoefficient h * affinityJ u)) := by
  let u := thermalBias h ^ 2
  let a := sharpCoefficient h
  have hu : u ∈ Ico (0 : ℝ) 1 := exactAffinity_bias_sq_mem hh
  have hs := affinityRoot_pos hu.1
  have hf : Tendsto (radialDeficitOfSquare h) (𝓝[>] u) (𝓝 0) := by
    simpa only [u, radialDeficitOfSquare_bias hh] using
      (continuous_radialDeficitOfSquare h).continuousAt.tendsto.mono_left
        (show 𝓝[>] u ≤ 𝓝 u from nhdsWithin_le_nhds)
  have hq : Continuous affinityRoot := by unfold affinityRoot; fun_prop
  have hq' : Tendsto affinityRoot (𝓝[>] u) (𝓝 (affinityRoot u)) :=
    hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun w => radialAffinityDefect u w ^ 2) (𝓝[>] u) (𝓝 0) := by
    have ht : Tendsto (radialAffinityDefect u) (𝓝[>] u)
        (𝓝 (1 - affinityRoot u / affinityRoot u)) :=
      (tendsto_const_nhds (x := (1 : ℝ))).sub
        ((tendsto_const_nhds (x := affinityRoot u)).div hq' hs.ne')
    simpa only [div_self hs.ne', sub_self, zero_pow (by decide : 2 ≠ 0)] using ht.pow 2
  have hlim : Tendsto (radialAffinitySlopeRatio a u) (𝓝[>] u) (𝓝 (4 * a * affinityJ u)) := by
    have he : 4 * a * affinityJ u =
        2 * a * (affinityRoot u + affinityRoot u) * affinityJ u / affinityRoot u := by
      field_simp [hs.ne'] <;> ring
    rw [he]
    exact (((tendsto_const_nhds (x := 2 * a)).mul
      (hq'.add (tendsto_const_nhds (x := affinityRoot u)))).mul
      (affinitySecant_tendsto hu)).div_const (affinityRoot u)
  refine HasDerivAt.lhopital_zero_nhdsGT
    (f' := fun w => radialAffinitySlopeRatio a u w * radialAffinitySquareSlope u w)
    (g' := radialAffinitySquareSlope u) ?_ ?_ ?_ hf hg ?_
  · filter_upwards [Ioo_mem_nhdsGT hu.2] with w hw
    exact radialDeficitOfSquare_hasDerivAt_ratio hh ⟨hu.1.trans_lt hw.1, hw.2⟩
  · filter_upwards [Ioo_mem_nhdsGT hu.2] with w hw
    exact radialAffinitySquare_hasDerivAt u (hu.1.trans hw.1.le)
  · filter_upwards [Ioo_mem_nhdsGT hu.2] with w hw
    exact (radialAffinitySquareSlope_pos hu.1 hw.1).ne'
  · apply hlim.congr'
    filter_upwards [Ioo_mem_nhdsGT hu.2] with w hw
    exact (mul_div_cancel_right₀ _ (radialAffinitySquareSlope_pos hu.1 hw.1).ne').symm

private theorem sq_tendsto_nhdsGT {k : ℝ} (hk : 0 ≤ k) :
    Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] k) (𝓝[>] (k ^ 2)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_id.pow 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact pow_lt_pow_left₀ (show k < t from ht) hk (by decide : 2 ≠ 0)

/-- Sharp radial limit as the square-root polarization decreases to the Gibbs value. -/
theorem radialDeficit_exactAffinity_limit {h : ℝ} (hh : 0 ≤ h) :
    let k := thermalBias h
    Tendsto (fun t => radialDeficit h (polarizationOfHalf t) /
      radialAffinityDefect (k ^ 2) (t ^ 2) ^ 2)
      (𝓝[>] k) (𝓝 (4 * sharpCoefficient h * affinityJ (k ^ 2))) := by
  let k := thermalBias h
  have hk : k ∈ Ico (0 : ℝ) 1 := exactAffinity_bias_mem hh
  apply ((radialDeficitOfSquare_exactAffinity_limit hh).comp (sq_tendsto_nhdsGT hk.1)).congr'
  filter_upwards [Ioo_mem_nhdsGT hk.2] with t ht
  simp [Function.comp_def, radialDeficitOfSquare, Real.sqrt_sq (hk.1.trans ht.1.le)]


private def exactAffinityRadialCoefficient (h : ℝ) : ℝ :=
  4 * sharpCoefficient h * affinityJ (thermalBias h ^ 2)

private theorem exactAffinityRadialCoefficient_pos {h : ℝ} (hh : 0 ≤ h) :
    0 < exactAffinityRadialCoefficient h :=
  mul_pos (mul_pos (by norm_num) (exactAffinity_sharpCoefficient_pos hh))
    (affinityJ_pos (exactAffinity_bias_sq_mem hh))

private def exactAffinityAngularReciprocal (h : ℝ) : ℝ :=
  Real.cosh h * thermalBias h ^ 2 / (1 + thermalBias h ^ 2)

private theorem exactAffinityAngularReciprocal_nonneg (h : ℝ) :
    0 ≤ exactAffinityAngularReciprocal h := by
  unfold exactAffinityAngularReciprocal
  positivity

/-- The sharp coefficient for the global scalar one-mode affinity bound. -/
def exactAffinityCoefficient (h : ℝ) : ℝ :=
  (exactAffinityAngularReciprocal h + 1 / exactAffinityRadialCoefficient h)⁻¹

theorem exactAffinityCoefficient_eq (h : ℝ) :
    exactAffinityCoefficient h =
      (Real.cosh h * thermalBias h ^ 2 / (1 + thermalBias h ^ 2) +
        1 / (4 * sharpCoefficient h * affinityJ (thermalBias h ^ 2)))⁻¹ := rfl

theorem exactAffinityCoefficient_pos {h : ℝ} (hh : 0 ≤ h) : 0 < exactAffinityCoefficient h :=
  inv_pos.mpr (add_pos_of_nonneg_of_pos (exactAffinityAngularReciprocal_nonneg h)
    (one_div_pos.mpr (exactAffinityRadialCoefficient_pos hh)))

theorem exactAffinityCoefficient_zero : exactAffinityCoefficient 0 = 4 / 3 := by
  norm_num [exactAffinityCoefficient, exactAffinityAngularReciprocal,
    exactAffinityRadialCoefficient, sharpCoefficient, thermalBias, affinityJ_zero]

/-- The scalar affinity defect in square-root polarization. -/
def normalizedAffinityDefect (h t z : ℝ) : ℝ :=
  1 - (1 + t * thermalBias h * z) /
    Real.sqrt ((1 + t ^ 2) * (1 + thermalBias h ^ 2))

private def affinityAngularWeight (h t : ℝ) : ℝ :=
  1 / (Real.cosh h * (1 + t ^ 2))

private def affinityAngularFactor (h t : ℝ) : ℝ :=
  thermalBias h / (affinityRoot (t ^ 2) * affinityRoot (thermalBias h ^ 2))

private theorem affinityAngularWeight_pos (h t : ℝ) : 0 < affinityAngularWeight h t := by
  unfold affinityAngularWeight
  positivity

private theorem affinityAngularFactor_nonneg {h : ℝ} (hh : 0 ≤ h) (t : ℝ) :
    0 ≤ affinityAngularFactor h t :=
  div_nonneg (exactAffinity_bias_mem hh).1
    (mul_pos (affinityRoot_pos (sq_nonneg t)) (affinityRoot_pos (sq_nonneg _))).le

private theorem affinityAngularFactor_sq_div_weight (h t : ℝ) :
    affinityAngularFactor h t ^ 2 / affinityAngularWeight h t =
      exactAffinityAngularReciprocal h := by
  unfold affinityAngularFactor affinityAngularWeight exactAffinityAngularReciprocal
  rw [div_pow, mul_pow, affinityRoot_sq (sq_nonneg t), affinityRoot_sq (sq_nonneg (thermalBias h))]
  field_simp [show 1 + t ^ 2 ≠ 0 by positivity, show 1 + thermalBias h ^ 2 ≠ 0 by positivity,
    (Real.cosh_pos h).ne'] <;> ring

private theorem normalizedAffinityDefect_eq_add (h t z : ℝ) :
    normalizedAffinityDefect h t z =
      radialAffinityDefect (thermalBias h ^ 2) (t ^ 2) +
        affinityAngularFactor h t * (thermalBias h - t * z) := by
  have ht := affinityRoot_pos (sq_nonneg t)
  have hk := affinityRoot_pos (sq_nonneg (thermalBias h))
  unfold normalizedAffinityDefect radialAffinityDefect affinityAngularFactor
  rw [Real.sqrt_mul (by positivity : 0 ≤ 1 + t ^ 2)]
  change 1 - (1 + t * thermalBias h * z) /
      (affinityRoot (t ^ 2) * affinityRoot (thermalBias h ^ 2)) =
    1 - affinityRoot (thermalBias h ^ 2) / affinityRoot (t ^ 2) +
      thermalBias h / (affinityRoot (t ^ 2) * affinityRoot (thermalBias h ^ 2)) *
        (thermalBias h - t * z)
  have hratio : affinityRoot (thermalBias h ^ 2) / affinityRoot (t ^ 2) =
      (1 + thermalBias h ^ 2) / (affinityRoot (t ^ 2) * affinityRoot (thermalBias h ^ 2)) := by
    rw [← affinityRoot_sq (sq_nonneg (thermalBias h))]
    field_simp [ht.ne', hk.ne'] <;> ring
  rw [hratio]
  ring

private theorem normalizedAffinityDefect_nonneg {h t z : ℝ} (hh : 0 ≤ h)
    (ht : 0 ≤ t) (hz : z ≤ 1) : 0 ≤ normalizedAffinityDefect h t z := by
  let k := thermalBias h
  have hk : 0 ≤ k := (exactAffinity_bias_mem hh).1
  have hden : 0 < Real.sqrt ((1 + t ^ 2) * (1 + k ^ 2)) := Real.sqrt_pos_of_pos (by positivity)
  unfold normalizedAffinityDefect
  apply sub_nonneg.mpr ((div_le_one₀ hden).mpr ?_)
  calc
    1 + t * k * z ≤ 1 + t * k := by
      simpa [add_comm] using add_le_add_left
        (mul_le_mul_of_nonneg_left hz (mul_nonneg ht hk)) 1
    _ ≤ _ := Real.le_sqrt_of_sq_le (by nlinarith only [sq_nonneg (t - k)])

/-- Complementary polarization in the square-root coordinate. -/
theorem spectralRoot_polarizationOfHalf {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    spectralRoot (polarizationOfHalf t) = (1 - t ^ 2) / (1 + t ^ 2) := by
  have hp := affinity_unit_sq (polarizationOfHalf_mem ht)
  unfold spectralRoot
  apply (Real.sqrt_eq_iff_eq_sq (sub_nonneg.mpr hp)
    (div_nonneg (sub_nonneg.mpr (affinity_unit_sq ht)) (by positivity))).mpr
  unfold polarizationOfHalf
  field_simp [show 1 + t ^ 2 ≠ 0 by positivity] <;> ring

private theorem normalizedDeficit_eq_radial_add_half_square (h : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (z : ℝ) :
    normalizedDeficit h (polarizationOfHalf t) z =
      radialDeficit h (polarizationOfHalf t) +
        affinityAngularWeight h t * (thermalBias h - t * z) ^ 2 := by
  rw [normalizedDeficit_eq_radial_add_square h (polarizationOfHalf_mem ht) z,
    spectralRoot_polarizationOfHalf ht]
  unfold polarizationOfHalf affinityAngularWeight
  have ht₁ : 1 + t ^ 2 ≠ 0 := by positivity
  have hs : 1 + (1 - t ^ 2) / (1 + t ^ 2) = 2 / (1 + t ^ 2) := by
    field_simp [ht₁] <;> ring
  rw [hs]
  field_simp [ht₁, (Real.cosh_pos h).ne'] <;> ring

private theorem radialAffinityDefect_nonpos {t k : ℝ} (ht : 0 ≤ t) (htk : t ≤ k) :
    radialAffinityDefect (k ^ 2) (t ^ 2) ≤ 0 := by
  unfold radialAffinityDefect
  apply sub_nonpos.mpr ((one_le_div (affinityRoot_pos (sq_nonneg t))).mpr ?_)
  apply Real.sqrt_le_sqrt
  exact add_le_add_right (pow_le_pow_left₀ ht htk 2) 1

private theorem weighted_affinity_square (r e B b y : ℝ) (hr : r ≠ 0) (he : e ≠ 0) :
    (1 / r + b ^ 2 / e) * (r * B ^ 2 + e * y ^ 2) - (B + b * y) ^ 2 =
      (e * y - r * B * b) ^ 2 / (r * e) := by
  field_simp [hr, he] <;> ring

/-- Exact global scalar bound, with strictness away from the Gibbs state. -/
theorem normalizedDeficit_exactAffinity_of_half {h t z : ℝ} (hh : 0 ≤ h)
    (ht : t ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (-1 : ℝ) 1) :
    let v := polarizationOfHalf t
    exactAffinityCoefficient h * normalizedAffinityDefect h t z ^ 2 ≤ normalizedDeficit h v z ∧
      (¬ (v = Real.tanh h ∧ (h = 0 ∨ z = 1)) →
        exactAffinityCoefficient h * normalizedAffinityDefect h t z ^ 2 <
          normalizedDeficit h v z) := by
  let k := thermalBias h
  let v := polarizationOfHalf t
  let G := radialDeficit h v
  let B := radialAffinityDefect (k ^ 2) (t ^ 2)
  let b := affinityAngularFactor h t
  let e := affinityAngularWeight h t
  let y := k - t * z
  let R := normalizedAffinityDefect h t z
  let δ := normalizedDeficit h v z
  let r := exactAffinityRadialCoefficient h
  let A := exactAffinityAngularReciprocal h
  let T := A + 1 / r
  have he : 0 < e := affinityAngularWeight_pos h t
  have hr : 0 < r := exactAffinityRadialCoefficient_pos hh
  have hA : 0 ≤ A := exactAffinityAngularReciprocal_nonneg h
  have hTr : A < T := lt_add_of_pos_right _ (one_div_pos.mpr hr)
  have hT : 0 < T := hA.trans_lt hTr
  have hδ : δ = G + e * y ^ 2 := normalizedDeficit_eq_radial_add_half_square h ht z
  have hR : R = B + b * y := normalizedAffinityDefect_eq_add h t z
  have hA' : b ^ 2 / e = A := affinityAngularFactor_sq_div_weight h t
  have hv : v ∈ Icc (0 : ℝ) 1 := polarizationOfHalf_mem ht
  change T⁻¹ * R ^ 2 ≤ δ ∧
    (¬ (v = Real.tanh h ∧ (h = 0 ∨ z = 1)) → T⁻¹ * R ^ 2 < δ)
  have hdiv : T⁻¹ * R ^ 2 = R ^ 2 / T := by rw [div_eq_mul_inv, mul_comm]
  rw [hdiv]
  by_cases hkt : k < t
  · have hrad := radialDeficit_gt_exactAffinity hh ⟨hkt, ht.2⟩
    change r * B ^ 2 < G at hrad
    have hweighted := weighted_affinity_square r e B b y hr.ne' he.ne'
    rw [hA', add_comm (1 / r) A, ← hR] at hweighted
    have hle : R ^ 2 ≤ T * (r * B ^ 2 + e * y ^ 2) := by
      apply sub_nonneg.mp
      change 0 ≤ (A + 1 / r) * (r * B ^ 2 + e * y ^ 2) - R ^ 2
      rw [hweighted]
      exact div_nonneg (sq_nonneg _) (mul_pos hr he).le
    have hlt : R ^ 2 < δ * T := by
      rw [hδ, mul_comm _ T]
      have hadd : r * B ^ 2 + e * y ^ 2 < G + e * y ^ 2 := by linarith
      exact hle.trans_lt (mul_lt_mul_of_pos_left hadd hT)
    exact ⟨((div_lt_iff₀ hT).mpr hlt).le, fun _ => (div_lt_iff₀ hT).mpr hlt⟩
  · have hR0 : 0 ≤ R := normalizedAffinityDefect_nonneg hh ht.1 hz.2
    have hBy : R ≤ b * y := by
      rw [hR]
      exact add_le_of_nonpos_left (radialAffinityDefect_nonpos ht.1 (le_of_not_gt hkt))
    have hle : R ^ 2 ≤ A * δ := calc
      R ^ 2 ≤ (b * y) ^ 2 := pow_le_pow_left₀ hR0 hBy 2
      _ = A * (e * y ^ 2) := by
        rw [mul_pow, (div_eq_iff he.ne').mp hA']
        ring
      _ ≤ A * δ := by
        rw [hδ]
        exact mul_le_mul_of_nonneg_left
          (le_add_of_nonneg_left (radialDeficit_nonneg hh hv)) hA
    constructor
    · apply (div_le_iff₀ hT).mpr
      rw [mul_comm δ T]
      exact hle.trans (mul_le_mul_of_nonneg_right hTr.le (normalizedDeficit_nonneg hh hv z))
    · intro hne
      apply (div_lt_iff₀ hT).mpr
      rw [mul_comm δ T]
      exact hle.trans_lt (mul_lt_mul_of_pos_right hTr (normalizedDeficit_pos_of_ne hh hv z hne))

theorem normalizedDeficit_exactAffinity {h v z : ℝ} (hh : 0 ≤ h)
    (hv : v ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (-1 : ℝ) 1) :
    let t := v / (1 + spectralRoot v)
    exactAffinityCoefficient h * normalizedAffinityDefect h t z ^ 2 ≤ normalizedDeficit h v z ∧
      (¬ (v = Real.tanh h ∧ (h = 0 ∨ z = 1)) →
        exactAffinityCoefficient h * normalizedAffinityDefect h t z ^ 2 <
          normalizedDeficit h v z) := by
  obtain ⟨ht, hp, _⟩ := exactAffinity_half_polarization hv
  simpa only [hp] using normalizedDeficit_exactAffinity_of_half hh ht hz



private def exactAffinityRadialRatio (h t : ℝ) : ℝ :=
  radialDeficit h (polarizationOfHalf t) /
    radialAffinityDefect (thermalBias h ^ 2) (t ^ 2) ^ 2

private def exactAffinitySharpDisplacement (h t : ℝ) : ℝ :=
  exactAffinityRadialRatio h t * radialAffinityDefect (thermalBias h ^ 2) (t ^ 2) *
    affinityAngularFactor h t / affinityAngularWeight h t

/-- Gibbs-axis cosine for the sharpness path on the higher-polarization side. -/
def exactAffinitySharpAlignment (h t : ℝ) : ℝ :=
  (thermalBias h - exactAffinitySharpDisplacement h t) / t

private theorem exactAffinitySharpDisplacement_tendsto {h : ℝ} (hh : 0 ≤ h) :
    Tendsto (exactAffinitySharpDisplacement h) (𝓝[>] (thermalBias h)) (𝓝 0) := by
  let k := thermalBias h
  have hk := affinityRoot_pos (sq_nonneg k)
  have hq : Continuous (fun t : ℝ => affinityRoot (t ^ 2)) := by
    unfold affinityRoot
    fun_prop
  have hB : ContinuousAt (fun t : ℝ => radialAffinityDefect (k ^ 2) (t ^ 2)) k := by
    unfold radialAffinityDefect
    exact continuousAt_const.sub (continuousAt_const.div hq.continuousAt hk.ne')
  have hb : ContinuousAt (affinityAngularFactor h) k := by
    unfold affinityAngularFactor
    exact continuousAt_const.div (hq.continuousAt.mul continuousAt_const) (mul_pos hk hk).ne'
  have he : Continuous (affinityAngularWeight h) := by
    unfold affinityAngularWeight
    exact continuous_const.div (by fun_prop) (fun _ => by positivity)
  have hB0 : radialAffinityDefect (k ^ 2) (k ^ 2) = 0 := by
    simp [radialAffinityDefect, hk.ne']
  have hlim := (((radialDeficit_exactAffinity_limit hh).mul
    (hB.tendsto.mono_left nhdsWithin_le_nhds)).mul
    (hb.tendsto.mono_left nhdsWithin_le_nhds)).div
    (he.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) (affinityAngularWeight_pos h k).ne'
  change Tendsto (exactAffinitySharpDisplacement h) (𝓝[>] k)
    (𝓝 ((4 * sharpCoefficient h * affinityJ (k ^ 2)) *
      radialAffinityDefect (k ^ 2) (k ^ 2) * affinityAngularFactor h k /
        affinityAngularWeight h k)) at hlim
  simpa only [hB0, mul_zero, zero_mul, zero_div] using hlim

theorem exactAffinitySharpAlignment_tendsto_one {h : ℝ} (hh : 0 < h) :
    Tendsto (exactAffinitySharpAlignment h) (𝓝[>] (thermalBias h)) (𝓝 1) := by
  let k := thermalBias h
  have hk : 0 < k := by
    dsimp [k]
    rw [exactAffinity_bias_eq_tanh_half]
    exact tanh_pos (by positivity)
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] k) (𝓝 k) :=
    tendsto_id.mono_right nhdsWithin_le_nhds
  have hl := (tendsto_const_nhds (x := k)).sub (exactAffinitySharpDisplacement_tendsto hh.le)
  have hlim : Tendsto (exactAffinitySharpAlignment h) (𝓝[>] k) (𝓝 ((k - 0) / k)) :=
    hl.div ht hk.ne'
  simpa only [sub_zero, div_self hk.ne'] using hlim

private theorem exactAffinitySharp_path {h : ℝ} (hh : 0 ≤ h) :
    ∀ᶠ t in 𝓝[>] (thermalBias h),
      t ∈ Icc (0 : ℝ) 1 ∧ polarizationOfHalf t ∈ Ico (0 : ℝ) 1 ∧
        exactAffinitySharpAlignment h t ∈ Icc (-1 : ℝ) 1 ∧
        0 < normalizedAffinityDefect h t (exactAffinitySharpAlignment h t) ∧
        normalizedDeficit h (polarizationOfHalf t) (exactAffinitySharpAlignment h t) /
          normalizedAffinityDefect h t (exactAffinitySharpAlignment h t) ^ 2 =
            (exactAffinityAngularReciprocal h + 1 / exactAffinityRadialRatio h t)⁻¹ := by
  let k := thermalBias h
  have hk : k ∈ Ico (0 : ℝ) 1 := exactAffinity_bias_mem hh
  have hupper : ∀ᶠ t in 𝓝[>] k, exactAffinitySharpDisplacement h t ≤ k + t := by
    rcases eq_or_lt_of_le hk.1 with hk0 | hkpos
    · filter_upwards [Ioo_mem_nhdsGT hk.2] with t ht
      have hb0 : affinityAngularFactor h t = 0 := by
        change k / _ = 0
        rw [← hk0, zero_div]
      have hy0 : exactAffinitySharpDisplacement h t = 0 := by
        simp [exactAffinitySharpDisplacement, hb0]
      simpa only [hy0, ← hk0, zero_add] using ht.1.le
    · have htlim : Tendsto (fun t : ℝ => k + t) (𝓝[>] k) (𝓝 (k + k)) :=
        tendsto_const_nhds.add (tendsto_id.mono_right nhdsWithin_le_nhds)
      exact ((exactAffinitySharpDisplacement_tendsto hh).eventually_lt htlim
        (add_pos hkpos hkpos)).mono (fun _ ht => ht.le)
  filter_upwards [Ioo_mem_nhdsGT hk.2, hupper] with t ht hyupper
  let v := polarizationOfHalf t
  let z := exactAffinitySharpAlignment h t
  let B := radialAffinityDefect (k ^ 2) (t ^ 2)
  let b := affinityAngularFactor h t
  let e := affinityAngularWeight h t
  let r := exactAffinityRadialRatio h t
  let y := exactAffinitySharpDisplacement h t
  let R := normalizedAffinityDefect h t z
  let δ := normalizedDeficit h v z
  let A := exactAffinityAngularReciprocal h
  change y ≤ k + t at hyupper
  have ht0 : 0 < t := hk.1.trans_lt ht.1
  have htcc : t ∈ Icc (0 : ℝ) 1 := ⟨ht0.le, ht.2.le⟩
  have hv1 : v < 1 := by
    change 2 * t / (1 + t ^ 2) < 1
    exact (div_lt_one₀ (by positivity)).mpr (by
      nlinarith only [sq_pos_of_pos (sub_pos.mpr ht.2)])
  have hkt : k ^ 2 < t ^ 2 := pow_lt_pow_left₀ ht.1 hk.1 (by decide : 2 ≠ 0)
  have hB : 0 < B := radialAffinityDefect_pos (sq_nonneg k) hkt
  have he : 0 < e := affinityAngularWeight_pos h t
  have hb : 0 ≤ b := affinityAngularFactor_nonneg hh t
  have hA : b ^ 2 / e = A := affinityAngularFactor_sq_div_weight h t
  have hrad := radialDeficit_gt_exactAffinity hh ⟨ht.1, ht.2.le⟩
  have hG : 0 < radialDeficit h v :=
    (mul_pos (exactAffinityRadialCoefficient_pos hh) (pow_pos hB 2)).trans hrad
  have hr : 0 < r := div_pos hG (pow_pos hB 2)
  have hy : y = r * B * b / e := rfl
  have hy0 : 0 ≤ y := by
    rw [hy]
    exact div_nonneg (mul_nonneg (mul_nonneg hr.le hB.le) hb) he.le
  have hzy : k - t * z = y := by
    change k - t * ((k - y) / t) = y
    field_simp [ht0.ne'] <;> ring
  have hz : z ∈ Icc (-1 : ℝ) 1 := by
    change -1 ≤ (k - y) / t ∧ (k - y) / t ≤ 1
    exact ⟨(le_div_iff₀ ht0).mpr (by linarith only [hyupper]),
      (div_le_one₀ ht0).mpr (by linarith only [ht.1, hy0])⟩
  have hR : R = B + b * y := by
    change normalizedAffinityDefect h t z = _
    rw [normalizedAffinityDefect_eq_add, hzy]
  have hR0 : 0 < R := by
    rw [hR]
    exact add_pos_of_pos_of_nonneg hB (mul_nonneg hb hy0)
  refine ⟨htcc, ⟨(polarizationOfHalf_mem htcc).1, hv1⟩, hz, hR0, ?_⟩
  have hG' : r * B ^ 2 = radialDeficit h v := div_mul_cancel₀ _ (pow_pos hB 2).ne'
  have hδ : δ = r * B ^ 2 + e * y ^ 2 := by
    change normalizedDeficit h v z = _
    rw [normalizedDeficit_eq_radial_add_half_square h htcc z, hzy, hG']
  have hopt : e * y - r * B * b = 0 := by
    rw [hy]
    field_simp [he.ne'] <;> ring
  have hweighted := weighted_affinity_square r e B b y hr.ne' he.ne'
  rw [← hδ, ← hR, hA, add_comm (1 / r) A, hopt, zero_pow (by decide : 2 ≠ 0),
    zero_div] at hweighted
  have hcomplete : R ^ 2 = (A + 1 / r) * δ := (sub_eq_zero.mp hweighted).symm
  have hden : 0 < A + 1 / r :=
    add_pos_of_nonneg_of_pos (exactAffinityAngularReciprocal_nonneg h) (one_div_pos.mpr hr)
  change δ / R ^ 2 = (A + 1 / r)⁻¹
  apply (div_eq_iff (pow_pos hR0 2).ne').mpr
  rw [hcomplete, ← mul_assoc, inv_mul_cancel₀ hden.ne', one_mul]

theorem exactAffinitySharpAlignment_eventually {h : ℝ} (hh : 0 ≤ h) :
    ∀ᶠ t in 𝓝[>] (thermalBias h),
      polarizationOfHalf t ∈ Ico (0 : ℝ) 1 ∧
        exactAffinitySharpAlignment h t ∈ Icc (-1 : ℝ) 1 ∧
        0 < normalizedAffinityDefect h t (exactAffinitySharpAlignment h t) :=
  (exactAffinitySharp_path hh).mono fun _ ht => ⟨ht.2.1, ht.2.2.1, ht.2.2.2.1⟩

/-- The normalized quotient approaches the exact coefficient along faithful spectra. -/
theorem normalizedDeficit_exactAffinity_sharp_limit {h : ℝ} (hh : 0 ≤ h) :
    Tendsto (fun t =>
      normalizedDeficit h (polarizationOfHalf t) (exactAffinitySharpAlignment h t) /
        normalizedAffinityDefect h t (exactAffinitySharpAlignment h t) ^ 2)
      (𝓝[>] (thermalBias h)) (𝓝 (exactAffinityCoefficient h)) := by
  let r := exactAffinityRadialCoefficient h
  let A := exactAffinityAngularReciprocal h
  have hr : 0 < r := exactAffinityRadialCoefficient_pos hh
  have hsum : 0 < A + 1 / r :=
    add_pos_of_nonneg_of_pos (exactAffinityAngularReciprocal_nonneg h) (one_div_pos.mpr hr)
  have hrad : Tendsto (exactAffinityRadialRatio h) (𝓝[>] (thermalBias h)) (𝓝 r) :=
    radialDeficit_exactAffinity_limit hh
  have hlim : Tendsto (fun t => (A + 1 / exactAffinityRadialRatio h t)⁻¹)
      (𝓝[>] (thermalBias h)) (𝓝 (exactAffinityCoefficient h)) :=
    ((tendsto_const_nhds (x := A)).add
      ((tendsto_const_nhds (x := (1 : ℝ))).div hrad hr.ne')).inv₀ hsum.ne'
  exact hlim.congr' ((exactAffinitySharp_path hh).mono (fun _ ht => ht.2.2.2.2.symm))

/-- Optimality over the physical rectangle in square-root polarization. -/
theorem exactAffinityCoefficient_isGreatest {h : ℝ} (hh : 0 ≤ h) :
    IsGreatest {c : ℝ | ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (-1 : ℝ) 1,
      c * normalizedAffinityDefect h t z ^ 2 ≤ normalizedDeficit h (polarizationOfHalf t) z}
      (exactAffinityCoefficient h) := by
  refine ⟨?_, ?_⟩
  · intro t ht z hz
    exact (normalizedDeficit_exactAffinity_of_half hh ht hz).1
  · intro c hc
    apply ge_of_tendsto (normalizedDeficit_exactAffinity_sharp_limit hh)
    filter_upwards [exactAffinitySharp_path hh] with t ht
    exact (le_div_iff₀ (pow_pos ht.2.2.2.1 2)).mpr
      (hc t ht.1 (exactAffinitySharpAlignment h t) ht.2.2.1)

end ExactAffinity

end D5.S3.Quantum.Semigroups.WuQubitSharpTwoRigidity
