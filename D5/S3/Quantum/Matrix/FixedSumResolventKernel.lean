/- GID: D5/S3/Quantum/Matrix/FixedSumResolventKernel
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/FixedSumResolventKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.Layercake]
   utility: none
   digest: Layer cake expresses fixed-sum resolvent moments as integrals of convex quadratic-root lengths. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Complex.Norm
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Quantum.Matrix.FixedSumResolventKernel

open Set MeasureTheory
open scoped ENNReal

/-- The actual scalar shifted-resolvent product at fixed sum. -/
def resolvent (S r s : ℝ) : ℝ := r ^ 2 / (s ^ 2 + S * s + r ^ 2)

/-- The fixed-sum integrated resolvent moment; division at zero is immaterial. -/
def kernel (S : ℝ) (j : ℕ) (r : ℝ) : ℝ :=
  (∫ s in Ioi 0, resolvent S r s ^ j) / j

private lemma resolvent_nonneg {S : ℝ} (hS : 0 ≤ S) (r : ℝ) {s : ℝ}
    (hs : 0 ≤ s) : 0 ≤ resolvent S r s := by
  unfold resolvent
  positivity

private lemma resolvent_le_one {S : ℝ} (hS : 0 < S) (r : ℝ) {s : ℝ}
    (hs : 0 < s) : resolvent S r s ≤ 1 := by
  have hd : 0 < s ^ 2 + S * s + r ^ 2 := by positivity
  rw [resolvent, div_le_one hd]
  nlinarith [mul_pos hS hs]

private lemma measurable_resolvent (S r : ℝ) : Measurable (resolvent S r) := by
  unfold resolvent
  fun_prop

/-- All positive integer moments are integrable, including at zero radius. -/
theorem integrable_resolvent {S : ℝ} (hS : 0 < S) (r : ℝ) {j : ℕ}
    (hj : 1 ≤ j) : IntegrableOn (fun s => resolvent S r s ^ j) (Ioi 0) := by
  apply ((integrable_inv_one_add_sq.const_mul (r ^ 2 + 1)).integrableOn).mono'
    ((measurable_resolvent S r).pow_const j).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs0 : 0 < s := hs
  have hd : 0 < s ^ 2 + S * s + r ^ 2 := by positivity
  have hc : 0 < 1 + s ^ 2 := by positivity
  have h0 := resolvent_nonneg hS.le r hs0.le
  have h1 := resolvent_le_one hS r hs0
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _)]
  calc
    resolvent S r s ^ j ≤ resolvent S r s := pow_le_self₀ h0 h1 (by omega)
    _ ≤ (r ^ 2 + 1) * (1 + s ^ 2)⁻¹ := by
      rw [resolvent, ← div_eq_mul_inv, div_le_div_iff₀ hd hc]
      nlinarith [mul_nonneg (sq_nonneg r) (sq_nonneg r),
        mul_nonneg (show 0 ≤ r ^ 2 + 1 by positivity) (mul_nonneg hS.le hs0.le)]

private def levelLength (S r t : ℝ) : ℝ :=
  (Real.sqrt (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1)) - S) / 2

private lemma length_nonneg {S r t : ℝ} (hS : 0 ≤ S) (ht : t ∈ Ioo 0 1) :
    0 ≤ levelLength S r t := by
  have ht' : 0 ≤ t⁻¹ - 1 := by
    rw [sub_nonneg, one_le_inv₀ ht.1]
    exact ht.2.le
  have hh : S ≤ Real.sqrt (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1)) := by
    apply (Real.le_sqrt hS (by positivity)).mpr
    nlinarith [mul_nonneg (sq_nonneg r) ht']
  exact div_nonneg (sub_nonneg.mpr hh) (by norm_num)

private lemma superlevel {S r t s : ℝ} (hS : 0 < S) (ht : t ∈ Ioo 0 1)
    (hs : 0 < s) : t < resolvent S r s ↔ s < levelLength S r t := by
  have hd : 0 < s ^ 2 + S * s + r ^ 2 := by positivity
  have ht' : 0 ≤ t⁻¹ - 1 := by
    rw [sub_nonneg, one_le_inv₀ ht.1]
    exact ht.2.le
  have hq : 0 ≤ S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1) := by positivity
  have hroot := Real.sq_sqrt hq
  have hroot0 := Real.sqrt_nonneg (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1))
  rw [resolvent, lt_div_iff₀ hd]
  have he : t * (s ^ 2 + S * s + r ^ 2) < r ^ 2 ↔
      s ^ 2 + S * s < r ^ 2 * (t⁻¹ - 1) := by
    rw [mul_comm t, ← lt_div_iff₀ ht.1]
    have hid : r ^ 2 / t = r ^ 2 * (t⁻¹ - 1) + r ^ 2 := by ring
    rw [hid]
    constructor <;> intro h <;> linarith
  rw [he]
  unfold levelLength
  constructor
  · intro hquad
    have hpos : 0 ≤ 2 * s + S := by positivity
    have hlt : 2 * s + S < Real.sqrt (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1)) := by
      nlinarith only [hquad, hroot, hroot0, hpos]
    linarith
  · intro h
    have hquad : s ^ 2 + S * s < r ^ 2 * (t⁻¹ - 1) := by
      have hp : 0 < 2 * s + S := by positivity
      nlinarith only [h, hroot, hroot0, hp]
    exact hquad

private lemma length_convex {S t : ℝ} (ht : t ∈ Ioo 0 1) :
    ConvexOn ℝ (Ici 0) (fun r => levelLength S r t) := by
  have hc : 0 ≤ t⁻¹ - 1 := by
    rw [sub_nonneg, one_le_inv₀ ht.1]
    exact ht.2.le
  let c := 2 * Real.sqrt (t⁻¹ - 1)
  have hc2 : c ^ 2 = 4 * (t⁻¹ - 1) := by
    dsimp [c]
    rw [mul_pow, Real.sq_sqrt hc]
    ring
  have hn (r : ℝ) : ‖(⟨S, c * r⟩ : ℂ)‖ =
      Real.sqrt (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1)) := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    congr 1
    simp only [Complex.mk_re, Complex.mk_im, mul_pow, hc2]
    ring
  refine ⟨convex_Ici 0, ?_⟩
  intro x _ y _ a b ha hb hab
  have hv : (⟨S, c * (a * x + b * y)⟩ : ℂ) =
      a • (⟨S, c * x⟩ : ℂ) + b • (⟨S, c * y⟩ : ℂ) := by
    apply Complex.ext <;> simp only [Complex.add_re, Complex.add_im,
      Complex.real_smul_re, Complex.real_smul_im, Complex.mk_re, Complex.mk_im]
    · nlinarith only [hab]
    · ring
  have hh := norm_add_le (a • (⟨S, c * x⟩ : ℂ)) (b • (⟨S, c * y⟩ : ℂ))
  rw [← hv, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ha, abs_of_nonneg hb, hn, hn, hn] at hh
  simp only [smul_eq_mul, levelLength]
  nlinarith only [hh, hab]

private def density (S : ℝ) (j : ℕ) (r t : ℝ) : ℝ :=
  levelLength S r t * t ^ (j - 1)

private lemma density_nonneg {S : ℝ} (hS : 0 ≤ S) (j : ℕ) (r : ℝ)
    {t : ℝ} (ht : t ∈ Ioo 0 1) : 0 ≤ density S j r t :=
  mul_nonneg (length_nonneg hS ht) (pow_nonneg ht.1.le _)

private lemma measurable_density (S : ℝ) (j : ℕ) (r : ℝ) :
    Measurable (density S j r) := by
  unfold density levelLength
  fun_prop

private lemma level_measure {S : ℝ} (hS : 0 < S) (r : ℝ) {t : ℝ} (ht : 0 < t) :
    (volume.restrict (Ioi (0 : ℝ))) {s | t < resolvent S r s} =
      if t < 1 then ENNReal.ofReal (levelLength S r t) else 0 := by
  rw [Measure.restrict_apply (measurableSet_lt measurable_const (measurable_resolvent S r))]
  by_cases ht1 : t < 1
  · rw [if_pos ht1]
    have he : {s | t < resolvent S r s} ∩ Ioi 0 = Ioo 0 (levelLength S r t) := by
      ext s
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_Ioo]
      constructor
      · intro h
        exact ⟨h.2, (superlevel hS ⟨ht, ht1⟩ h.2).mp h.1⟩
      · intro h
        exact ⟨(superlevel hS ⟨ht, ht1⟩ h.1).mpr h.2, h.1⟩
    rw [he, Real.volume_Ioo, sub_zero]
  · rw [if_neg ht1]
    have he : {s | t < resolvent S r s} ∩ Ioi 0 = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro s hs
      exact not_lt_of_ge ((resolvent_le_one hS r hs.2).trans (le_of_not_gt ht1)) hs.1
    rw [he, measure_empty]

private lemma layercake_lintegral {S : ℝ} (hS : 0 < S) (r : ℝ) {j : ℕ}
    (hj : 1 ≤ j) :
    (∫⁻ s in Ioi 0, ENNReal.ofReal (resolvent S r s ^ j)) =
      ENNReal.ofReal (j : ℝ) * ∫⁻ t in Ioo 0 1, ENNReal.ofReal (density S j r t) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] resolvent S r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact resolvent_nonneg hS.le r (le_of_lt hs)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hh := lintegral_rpow_eq_lintegral_meas_lt_mul
    (volume.restrict (Ioi (0 : ℝ))) hnn (measurable_resolvent S r).aemeasurable hj0
  have he : (j : ℝ) - 1 = ((j - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hj, Nat.cast_one]
  simp_rw [he, Real.rpow_natCast] at hh
  rw [hh]
  congr 1
  rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr
  intro t
  by_cases ht : 0 < t
  · rw [indicator_of_mem ht, level_measure hS r ht]
    by_cases ht1 : t < 1
    · rw [if_pos ht1, indicator_of_mem (show t ∈ Ioo 0 1 from ⟨ht, ht1⟩)]
      exact (ENNReal.ofReal_mul (length_nonneg hS.le ⟨ht, ht1⟩)).symm
    · rw [if_neg ht1, zero_mul, indicator_of_notMem (show t ∉ Ioo 0 1 from fun h => ht1 h.2)]
  · rw [indicator_of_notMem ht, indicator_of_notMem (show t ∉ Ioo 0 1 from fun h => ht h.1)]

private lemma integrable_density {S : ℝ} (hS : 0 < S) (r : ℝ) {j : ℕ}
    (hj : 1 ≤ j) : IntegrableOn (density S j r) (Ioo 0 1) := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] density S j r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact density_nonneg hS.le j r ht
  apply (lintegral_ofReal_ne_top_iff_integrable
    (measurable_density S j r).aestronglyMeasurable.restrict hnn).mp
  intro he
  have hfin := (integrable_resolvent hS r hj).lintegral_lt_top
  rw [layercake_lintegral hS r hj, he] at hfin
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  simp [ENNReal.ofReal_pos.mpr hj0 |>.ne'] at hfin

private lemma layercake {S : ℝ} (hS : 0 < S) (r : ℝ) {j : ℕ}
    (hj : 1 ≤ j) : kernel S j r = ∫ t in Ioo 0 1, density S j r t := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fun s => resolvent S r s ^ j := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact pow_nonneg (resolvent_nonneg hS.le r (le_of_lt hs)) j
  have hdn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] density S j r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact density_nonneg hS.le j r ht
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  unfold kernel
  rw [integral_eq_lintegral_of_nonneg_ae hnn
      (integrable_resolvent hS r hj).aestronglyMeasurable,
    layercake_lintegral hS r hj, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hj0.le,
    ← integral_eq_lintegral_of_nonneg_ae hdn
      (integrable_density hS r hj).aestronglyMeasurable]
  exact mul_div_cancel_left₀ _ hj0.ne'

/-- Fixed-sum resolvent moments are convex on the entire nonnegative half-line. -/
theorem convex_kernel {S : ℝ} (hS : 0 < S) {j : ℕ} (hj : 1 ≤ j) :
    ConvexOn ℝ (Ici 0) (kernel S j) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  rw [layercake hS _ hj, layercake hS _ hj, layercake hS _ hj]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_density hS x hj).const_mul a)
      ((integrable_density hS y hj).const_mul b)]
  apply setIntegral_mono_on (integrable_density hS _ hj)
    (((integrable_density hS x hj).const_mul a).add
      ((integrable_density hS y hj).const_mul b)) measurableSet_Ioo
  intro t ht
  have hh := (length_convex ht).2 hx hy ha hb hab
  simp only [smul_eq_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg ht.1.le (j - 1))
  dsimp only [density]
  nlinarith only [hm]

private lemma kernel_scale {S c : ℝ} (hS : 0 < S) (hc : 0 < c)
    (r : ℝ) {j : ℕ} (hj : 1 ≤ j) : kernel (c * S) j (c * r) = c * kernel S j r := by
  rw [layercake (mul_pos hc hS) _ hj, layercake hS _ hj, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht' : 0 ≤ t⁻¹ - 1 := by
    rw [sub_nonneg, one_le_inv₀ ht.1]
    exact ht.2.le
  have he : (c * S) ^ 2 + 4 * (c * r) ^ 2 * (t⁻¹ - 1) =
      c ^ 2 * (S ^ 2 + 4 * r ^ 2 * (t⁻¹ - 1)) := by ring
  dsimp [density, levelLength]
  rw [he, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  ring

private lemma kernel_zero (S : ℝ) (j : ℕ) : kernel S j 0 = 0 := by
  by_cases hj : j = 0
  · simp [kernel, hj]
  · simp [kernel, resolvent, zero_pow hj]

private lemma denominator_comparison {S P T : ℝ} (hS : 0 < S) (hP : 0 < P)
    (hT : T ^ 2 ≤ P) {j : ℕ} (hj : 1 ≤ j) :
    (T ^ 2 / P) ^ j * kernel S j (Real.sqrt P) ≤ kernel S j T := by
  have hp := Real.sq_sqrt hP.le
  have hint1 := integrable_resolvent hS (Real.sqrt P) hj
  have hint2 := integrable_resolvent hS T hj
  unfold kernel
  rw [← mul_div_assoc, ← integral_const_mul]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply setIntegral_mono_on (hint1.const_mul _) hint2 measurableSet_Ioi
  intro s hs
  have hd : 0 < s ^ 2 + S * s + T ^ 2 := by positivity
  have hdp : 0 < s ^ 2 + S * s + P := by positivity
  have he : (T ^ 2 / P) * resolvent S (Real.sqrt P) s =
      T ^ 2 / (s ^ 2 + S * s + P) := by
    rw [resolvent, hp]
    field_simp [hP.ne', hdp.ne']
  rw [← mul_pow]
  apply pow_le_pow_left₀ (mul_nonneg (by positivity)
    (resolvent_nonneg hS.le _ (le_of_lt hs)))
  rw [he, resolvent]
  exact div_le_div_of_nonneg_left (sq_nonneg T) hd (by linarith)

/-- Scalar moment of two possibly singular, nonnegative eigenvalues. -/
def scalarMoment (j : ℕ) (u v : ℝ) : ℝ :=
  (∫ s in Ioi 0, (u * v / ((s + u) * (s + v))) ^ j) / j

private lemma scalar_integrand {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (s : ℝ) :
    u * v / ((s + u) * (s + v)) = resolvent (u + v) (Real.sqrt (u * v)) s := by
  rw [resolvent, Real.sq_sqrt (mul_nonneg hu hv)]
  congr 1
  ring

private lemma scalar_eq_kernel {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (j : ℕ) :
    scalarMoment j u v = kernel (u + v) j (Real.sqrt (u * v)) := by
  simp only [scalarMoment, kernel, scalar_integrand hu hv]

/-- Scalar resolvent moments have derived integrability even when either input vanishes. -/
theorem integrable_scalar {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v)
    {j : ℕ} (hj : 1 ≤ j) :
    IntegrableOn (fun s => (u * v / ((s + u) * (s + v))) ^ j) (Ioi 0) := by
  by_cases h : u + v = 0
  · have hu0 : u = 0 := by linarith
    simp [hu0, zero_pow (show j ≠ 0 by omega)]
  · simp_rw [scalar_integrand hu hv]
    exact integrable_resolvent (lt_of_le_of_ne (add_nonneg hu hv) (Ne.symm h)) _ hj

/-- Weighted Jensen and denominator comparison yield every commuting spectral moment bound. -/
theorem scalar_fidelity_moment {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hα : 0 < ∑ i, a i) (hβ : 0 < ∑ i, b i) {j : ℕ} (hj : 1 ≤ j) :
    scalarMoment j (∑ i, a i) (∑ i, b i) *
      ((∑ i, Real.sqrt (a i * b i)) ^ 2 / ((∑ i, a i) * ∑ i, b i)) ^ j ≤
      ∑ i, scalarMoment j (a i) (b i) := by
  classical
  let α := ∑ i, a i
  let β := ∑ i, b i
  let S := α + β
  let w := fun i => (a i + b i) / S
  let r := fun i => Real.sqrt (a i * b i) / w i
  let T := ∑ i, Real.sqrt (a i * b i)
  have hS : 0 < S := add_pos hα hβ
  have hw (i : ι) : 0 ≤ w i := div_nonneg (add_nonneg (ha i) (hb i)) hS.le
  have hwS (i : ι) : w i * S = a i + b i := by
    exact div_mul_cancel₀ _ hS.ne'
  have hsum : ∑ i, w i = 1 := by
    dsimp [w, S, α, β]
    rw [← Finset.sum_div, Finset.sum_add_distrib, div_self hS.ne']
  have hz (i : ι) (hi : w i = 0) : a i = 0 ∧ b i = 0 := by
    have hh := hwS i
    rw [hi, zero_mul] at hh
    exact ⟨by linarith [ha i, hb i], by linarith [ha i, hb i]⟩
  have hwr (i : ι) : w i * r i = Real.sqrt (a i * b i) := by
    by_cases hi : w i = 0
    · simp [hi, (hz i hi).1]
    · exact mul_div_cancel₀ _ hi
  have hmoment (i : ι) : w i * kernel S j (r i) = scalarMoment j (a i) (b i) := by
    by_cases hi : w i = 0
    · simp [hi, (hz i hi).1, scalarMoment, zero_pow (show j ≠ 0 by omega)]
    · rw [← kernel_scale hS (lt_of_le_of_ne (hw i) (Ne.symm hi)) _ hj,
        hwS i, hwr i, scalar_eq_kernel (ha i) (hb i)]
  have hJ := (convex_kernel hS hj).map_sum_le (t := Finset.univ) (w := w) (p := r)
    (fun i _ => hw i) hsum (fun i _ => div_nonneg (Real.sqrt_nonneg _) (hw i))
  simp only [smul_eq_mul] at hJ
  simp_rw [hwr, hmoment] at hJ
  have hCS : T ≤ Real.sqrt (α * β) := by
    have hh := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset ι) ha hb
    calc
      T = ∑ i, Real.sqrt (a i) * Real.sqrt (b i) := by
        dsimp [T]
        apply Finset.sum_congr rfl
        intro i _
        exact Real.sqrt_mul (ha i) _
      _ ≤ Real.sqrt α * Real.sqrt β := hh
      _ = Real.sqrt (α * β) := (Real.sqrt_mul hα.le _).symm
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hP : 0 < α * β := mul_pos hα hβ
  have hT2 : T ^ 2 ≤ α * β := by
    nlinarith [Real.sq_sqrt hP.le, Real.sqrt_nonneg (α * β)]
  have hD := denominator_comparison hS hP hT2 hj
  rw [mul_comm, ← scalar_eq_kernel hα.le hβ.le j] at hD
  exact hD.trans hJ

end D5.S3.Quantum.Matrix.FixedSumResolventKernel
