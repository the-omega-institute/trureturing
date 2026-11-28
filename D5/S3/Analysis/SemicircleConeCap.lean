/- GID: D5/S3/Analysis/SemicircleConeCap
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-weak-boundary5-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Weak cap pairing for a semicircle angular projection. -/

import Batteries.Tactic.OpenPrivate
import OmegaBuild.Commands
import D5.S3.Analysis.ConeCapLimits
import D5.S3.Analysis.HalfPowerCapIntegral

/-!
Omega original.

Weak cap pairing for a semicircle angular projection.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Topology ENNReal NNReal

namespace Omega.ConeCap

open private densityError from OmegaMath.Analysis.HalfPowerCapIntegral

open private pair_radii_ae angularRemainder angularRemainder_measurable diagonalWeight
  diagonalWeight_measurable diagonalWeight_bound diagonalWeight_cancels
  diagonalCap_boundary affineLogIntegral_diagonal first_measurable second_measurable coincident
  from OmegaMath.Analysis.ConeCapLimits

variable {A : Type*} [MeasurableSpace A]

local instance (δ : ℝ) : IsFiniteMeasure (radialMeasure δ) :=
  inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo δ 1)))

local instance {σ : Measure A} [IsFiniteMeasure σ] (δ : ℝ) :
    IsFiniteMeasure (pairMeasure σ δ) := by unfold pairMeasure; infer_instance

private theorem measurable_halfPowerCap {X : Type*} [MeasurableSpace X]
    {t : X → ℝ} {d : X → ℂ} (ht : Measurable t) (hd : Measurable d) :
    Measurable (fun z => halfPowerCap (t z) (d z)) := by
  unfold halfPowerCap principalRoot
  exact ((Complex.continuous_ofReal.measurable.comp ht).add hd).inv.mul
    ((((Complex.continuous_ofReal.measurable.comp ht).add hd).pow_const _).inv)

/-- The pushed-forward angular cap integral with semicircle density. -/
private theorem mapped_halfPowerCap {σ : Measure A} {x : A → ℝ}
    (hx : Measurable x) {c : ℝ} (hc : 0 ≤ c)
    (hcap : Measure.map x σ = (volume.restrict (Icc (-1 : ℝ) 1)).withDensity
      (fun x => ENNReal.ofReal (c * Real.sqrt (1 - x ^ 2)))) {d : ℂ} (hd : 0 < d.re) :
    (∫ n, halfPowerCap (1 - x n) d ∂σ) =
      (c * Real.sqrt 2 : ℝ) * (semicircleCapFinitePart d - Complex.log d) := by
  let f : ℝ → ℂ := fun t => halfPowerCap (1 - t) d
  have hf : Measurable f := measurable_halfPowerCap (measurable_const.sub measurable_id)
    measurable_const
  change (∫ n, f (x n) ∂σ) = _
  rw [← integral_map hx.aemeasurable hf.aestronglyMeasurable, hcap,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have hsub := intervalIntegral.integral_comp_sub_left (a := (-1 : ℝ)) (b := 1)
    (fun t : ℝ => (ENNReal.ofReal (c * Real.sqrt (1 - (1 - t) ^ 2))).toReal • halfPowerCap t d) 1
  simp only [show (1 : ℝ) - 1 = 0 by norm_num, show (1 : ℝ) - -1 = 2 by norm_num] at hsub
  simp only [sub_sub_cancel, f] at hsub ⊢
  rw [hsub]
  · rw [← semicircleCapIntegral_eq hd]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
    dsimp only
    rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    have he : 1 - (1 - t) ^ 2 = (2 * t) * (1 - t / 2) := by ring
    rw [he, Real.sqrt_mul (by linarith [ht.1] : 0 ≤ 2 * t),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    push_cast
    ring

/-- The regulated angular denominator of degree three halves. -/
def halfCapIntegrand (f : ℝ × A → ℂ) (x : A → A → ℝ) (ε : ℝ) (z : Pair A) : ℂ :=
  (star (f (first z)) * f (second z)) *
    halfPowerCap (1 - x z.2.1 z.2.2) (capShift ε z.1.1 z.1.2)

set_option maxHeartbeats 1500000 in
private theorem angularRemainder_half_limit {σ : Measure A} [IsFiniteMeasure σ]
    {x : A → A → ℝ} (hx : Measurable (Function.uncurry x))
    (hangle : ∀ᵐ p ∂σ.prod σ, x p.1 p.2 < 1)
    (hmajor : Integrable (fun p : A × A => (1 - x p.1 p.2)⁻¹) (σ.prod σ))
    {f : ℝ × A → ℂ} (hf : Measurable f) {δ B C : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B)
    (hlip : ∀ r ∈ Ioo δ 1, ∀ n m, ‖f (r, m) - f (r, n)‖ ≤ C * Real.sqrt (1 - x n m))
    (hzero : ∀ n, (∫ r, f (r, n) ∂radialMeasure δ) = 0) :
    Tendsto (fun ε : ℝ => ∫ z, angularRemainder f z *
      halfPowerCap (1 - x z.2.1 z.2.2) (capShift ε z.1.1 z.1.2) ∂pairMeasure σ δ)
      (𝓝[>] 0) (𝓝 0) := by
  let μ := radialMeasure δ
  let R : Pair A → ℝ := fun z => 1 - x z.2.1 z.2.2
  let d : ℝ → Pair A → ℂ := fun ε z => capShift ε z.1.1 z.1.2
  let g (ε : ℝ) (z : Pair A) := angularRemainder f z * halfPowerCap (R z) (d ε z)
  have hr : Measurable R := (measurable_const.sub hx).comp measurable_snd
  have hd (ε : ℝ) : Measurable (d ε) := by dsimp [d, capShift]; fun_prop
  have hg (ε : ℝ) : Measurable (g ε) := (angularRemainder_measurable hf).mul
    (measurable_halfPowerCap hr (hd ε))
  have hp : ∀ᵐ z ∂pairMeasure σ δ, 0 < R z :=
    ((σ.prod σ).quasiMeasurePreserving_snd (μ := μ.prod μ)).ae
      (hangle.mono fun _ h => sub_pos.mpr h)
  have hbound (ε : ℝ) : ∀ᵐ z ∂pairMeasure σ δ, ‖g ε z‖ ≤ B * C * (R z)⁻¹ := by
    filter_upwards [pair_radii_ae σ δ, hp] with z hz hR
    have hre : 0 ≤ (d ε z).re := by
      dsimp only [d]
      rw [capShift_re]
      have hu := hδ.trans hz.1.1
      have hv := hδ.trans hz.2.1
      positivity
    have htest : ‖angularRemainder f z‖ ≤ B * (C * Real.sqrt (R z)) := by
      rw [angularRemainder, norm_mul, norm_star]
      exact mul_le_mul (hb _ hz.1 _) (hlip _ hz.2 _ _) (norm_nonneg _) hB
    dsimp only [g]
    rw [norm_mul]
    exact (mul_le_mul htest (halfPowerCap_norm_le hR hre) (norm_nonneg _)
      ((norm_nonneg _).trans htest)).trans_eq (by
      field_simp [hR.ne', (Real.sqrt_pos.2 hR).ne'])
  have hi : Integrable (fun z => B * C * (R z)⁻¹) (pairMeasure σ δ) :=
    (hmajor.comp_snd (μ.prod μ)).const_mul (B * C)
  have hlim : Tendsto (fun ε : ℝ => ∫ z, g ε z ∂pairMeasure σ δ)
      (𝓝[>] 0) (𝓝 (∫ z, g 0 z ∂pairMeasure σ δ)) := by
    refine tendsto_integral_filter_of_dominated_convergence _ (.of_forall fun ε =>
      (hg ε).aestronglyMeasurable) (.of_forall hbound) hi ?_
    filter_upwards [hp] with z hz
    have hc : ContinuousAt (fun ε => d ε z) 0 := (continuous_capShift _ _).continuousAt
    have he : d 0 z = 0 := by simp [d, capShift]
    have hd' : Tendsto (fun ε => d ε z) (𝓝[>] 0) (𝓝 0) :=
      he ▸ hc.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [g, he, Function.comp_apply] using ((halfPowerCap_continuousAt (d := 0)
      (by simpa using hz)).tendsto.comp hd').const_mul (angularRemainder f z)
  have hz : (∫ z, g 0 z ∂pairMeasure σ δ) = 0 := by
    have hg₀ := hi.mono' (hg 0).aestronglyMeasurable (hbound 0)
    change (∫ z, g 0 z ∂((μ.prod μ).prod (σ.prod σ))) = _
    rw [integral_prod_symm _ hg₀]
    apply integral_eq_zero_of_ae
    filter_upwards with p
    change (∫ r : ℝ × ℝ, (star (f (r.1, p.1)) * (f (r.2, p.2) - f (r.2, p.1))) *
      halfPowerCap (1 - x p.1 p.2) (capShift 0 r.1 r.2) ∂(μ.prod μ)) = 0
    simp only [capShift, zero_pow (by norm_num : 2 ≠ 0), zero_mul, Complex.ofReal_zero,
      mul_zero, add_zero, zero_div, integral_mul_const]
    rw [integral_prod_mul (fun r => star (f (r, p.1))) (fun r => f (r, p.2) - f (r, p.1))]
    dsimp only [Complex.star_def]
    rw [integral_conj, hzero p.1, map_zero, zero_mul, zero_mul]
  rw [hz] at hlim
  exact hlim

set_option maxHeartbeats 1500000 in
private theorem halfCapIntegrand_split {σ : Measure A} [IsFiniteMeasure σ]
    {x : A → A → ℝ} (hx : Measurable (Function.uncurry x)) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ n, Measure.map (x n) σ = (volume.restrict (Icc (-1 : ℝ) 1)).withDensity
      (fun x => ENNReal.ofReal (c * Real.sqrt (1 - x ^ 2))))
    {f : ℝ × A → ℂ} (hf : Measurable f) {δ B ε : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hε : 0 < ε) (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B)
    (hupper : ∀ n m, x n m ≤ 1) (hσ : 0 < σ.real univ) :
    (∫ z, halfCapIntegrand f x ε z ∂pairMeasure σ δ) =
      (∫ z, angularRemainder f z *
        halfPowerCap (1 - x z.2.1 z.2.2) (capShift ε z.1.1 z.1.2) ∂pairMeasure σ δ) +
      ((c * Real.sqrt 2 / σ.real univ : ℝ) : ℂ) * (∫ z, diagonalWeight f z *
        (semicircleCapFinitePart (capShift ε z.1.1 z.1.2) - Complex.log (capShift ε z.1.1 z.1.2))
        ∂pairMeasure σ δ) := by
  let μ := radialMeasure δ
  let D : Pair A → ℂ := fun z =>
    (1 - x z.2.1 z.2.2 : ℝ) + capShift ε z.1.1 z.1.2
  let H : ℝ × ℝ → ℂ := fun r =>
    semicircleCapFinitePart (capShift ε r.1 r.2) - Complex.log (capShift ε r.1 r.2)
  have hD : Measurable D := by
    apply (Complex.continuous_ofReal.measurable.comp ((measurable_const.sub hx).comp
      measurable_snd)).add
    unfold capShift
    fun_prop
  have hnorm : ∀ᵐ z ∂pairMeasure σ δ, ε ^ 2 / 2 ≤ ‖D z‖ := by
    filter_upwards [pair_radii_ae σ δ] with z hz
    apply le_trans _ (Complex.re_le_norm _)
    dsimp only [D]
    rw [Complex.add_re, Complex.ofReal_re, capShift_re]
    have hu := hδ.trans hz.1.1
    have hv := hδ.trans hz.2.1
    have hle : 2 * z.1.1 * z.1.2 ≤ 2 := by
      nlinarith [mul_le_mul hz.1.2.le hz.2.2.le hv.le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hle).trans
      (le_add_of_nonneg_left (sub_nonneg.mpr (hupper _ _)))
  have bound (g : Pair A → ℂ) (hg : Measurable g) {C : ℝ}
      (hC : ∀ᵐ z ∂pairMeasure σ δ, ‖g z‖ ≤ C) :
      Integrable (fun z => g z * (D z)⁻¹ * (principalRoot (D z))⁻¹) (pairMeasure σ δ) := by
    have hp : 0 < ε ^ 2 / 2 := by positivity
    apply (integrable_const (C * (ε ^ 2 / 2)⁻¹ * (Real.sqrt (ε ^ 2 / 2))⁻¹)).mono' ((hg.mul hD.inv).mul (hD.pow_const _).inv).aestronglyMeasurable
    filter_upwards [hnorm, hC] with z hz hb'
    change ‖g z * (D z)⁻¹ * (principalRoot (D z))⁻¹‖ ≤ _
    rw [norm_mul, norm_mul, norm_inv, norm_inv, principalRoot_norm]
    have hc' := (norm_nonneg _).trans hb'
    exact mul_le_mul (mul_le_mul hb' (inv_anti₀ hp hz) (by positivity) hc')
      (inv_anti₀ (Real.sqrt_pos.2 hp) (Real.sqrt_le_sqrt hz)) (by positivity) (by positivity)
  have hi := bound (diagonalWeight f) (diagonalWeight_measurable hf) (diagonalWeight_bound hB hb)
  have hj : Integrable (fun z => angularRemainder f z * (D z)⁻¹ * (principalRoot (D z))⁻¹) (pairMeasure σ δ) := by
    apply bound _ (angularRemainder_measurable hf) (C := B * (B + B))
    filter_upwards [pair_radii_ae σ δ] with z hz
    rw [angularRemainder, norm_mul, norm_star]
    exact mul_le_mul (hb _ hz.1 _) ((norm_sub_le _ _).trans (add_le_add (hb _ hz.2 _) (hb _ hz.2 _)))
      (norm_nonneg _) hB
  have hsplit : halfCapIntegrand f x ε = fun z =>
      angularRemainder f z * (D z)⁻¹ * (principalRoot (D z))⁻¹ + diagonalWeight f z * (D z)⁻¹ * (principalRoot (D z))⁻¹ := by
    funext z
    dsimp only [halfCapIntegrand, halfPowerCap, angularRemainder, diagonalWeight, D]
    ring
  rw [hsplit, integral_add hj hi]
  simp only [halfPowerCap, ← mul_assoc]
  rw [_root_.add_right_inj]
  have he : ∀ᵐ r ∂μ.prod μ,
      (∫ p : A × A, diagonalWeight f (r, p) * (D (r, p))⁻¹ * (principalRoot (D (r, p)))⁻¹ ∂σ.prod σ) =
      ((c * Real.sqrt 2 : ℝ) : ℂ) * (∫ n, star (f (r.1, n)) * f (r.2, n) ∂σ) * H r := by
    have hm : ∀ᵐ r ∂μ.prod μ, r.1 ∈ Ioo δ 1 ∧ r.2 ∈ Ioo δ 1 :=
      ((μ.quasiMeasurePreserving_fst (ν := μ)).ae (ae_restrict_mem measurableSet_Ioo)).and
      ((μ.quasiMeasurePreserving_snd (μ := μ)).ae (ae_restrict_mem measurableSet_Ioo))
    filter_upwards [hm, hi.prod_right_ae] with r hr hir
    rw [integral_prod _ hir]
    have hd : 0 < (capShift ε r.1 r.2).re := by
      rw [capShift_re]
      have hu := hδ.trans hr.1.1
      have hv := hδ.trans hr.2.1
      positivity
    have hcap' (n : A) := mapped_halfPowerCap
      (x := x n) (hx.comp (measurable_const.prodMk measurable_id)) hc.le (hcap n) hd
    have hinner (n : A) :
        (∫ m, diagonalWeight f (r, n, m) * (D (r, n, m))⁻¹ * (principalRoot (D (r, n, m)))⁻¹ ∂σ) =
          (((c * Real.sqrt 2 : ℝ) : ℂ) * H r) * (star (f (r.1, n)) * f (r.2, n)) := by
      simp only [D, diagonalWeight, first, coincident, mul_assoc (star (f _) * f _),
        integral_const_mul]
      change _ = _
      unfold halfPowerCap at hcap'
      rw [hcap' n]
      ring
    simp_rw [hinner, integral_const_mul]
    ring
  have hm (r : ℝ × ℝ) :
      (∫ p : A × A, diagonalWeight f (r, p) * H r ∂σ.prod σ) =
      (σ.real univ : ℂ) * (∫ n, star (f (r.1, n)) * f (r.2, n) ∂σ) * H r := by
    simp only [diagonalWeight, first, coincident, integral_mul_const]
    rw [integral_fun_fst (μ := σ) (ν := σ) (fun n => star (f (r.1, n)) * f (r.2, n))]
    rw [Complex.real_smul]
  have hdiag : Integrable (fun z => diagonalWeight f z * H z.1) (pairMeasure σ δ) := by
    have hp : ((c * Real.sqrt 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (mul_pos hc (Real.sqrt_pos.2 (by norm_num))).ne'
    have heq : (fun z => diagonalWeight f z * H z.1) =ᵐ[pairMeasure σ δ]
        fun z => ((c * Real.sqrt 2 : ℝ) : ℂ)⁻¹ * (∫ m, diagonalWeight f (z.1, z.2.1, m) *
          (D (z.1, z.2.1, m))⁻¹ * (principalRoot (D (z.1, z.2.1, m)))⁻¹ ∂σ) := by
      filter_upwards [pair_radii_ae σ δ] with z hz
      have hd : 0 < (capShift ε z.1.1 z.1.2).re := by
        rw [capShift_re]
        have hu := hδ.trans hz.1.1
        have hv := hδ.trans hz.2.1
        positivity
      have ht := mapped_halfPowerCap (x := x z.2.1) (hx.comp (measurable_const.prodMk measurable_id))
        hc.le (hcap z.2.1) hd
      simp only [D, diagonalWeight, first, coincident, mul_assoc (star (f _) * f _),
        integral_const_mul]
      unfold halfPowerCap at ht
      rw [ht]
      dsimp [H]
      field_simp [hp]
    have ha : Integrable (fun p : ((ℝ × ℝ) × A) × A =>
        diagonalWeight f (p.1.1, p.1.2, p.2) * (D (p.1.1, p.1.2, p.2))⁻¹ * (principalRoot (D (p.1.1, p.1.2, p.2)))⁻¹)
        (((μ.prod μ).prod σ).prod σ) :=
      (measurePreserving_prodAssoc (μ.prod μ) σ σ).integrable_comp_of_integrable hi
    have hfirst := (ha.integral_prod_left.const_mul ((c * Real.sqrt 2 : ℝ) : ℂ)⁻¹).comp_fst σ
    have hb' := ((measurePreserving_prodAssoc (μ.prod μ) σ σ).symm
      MeasurableEquiv.prodAssoc).integrable_comp_of_integrable hfirst
    exact hb'.congr heq.symm
  change (∫ z, diagonalWeight f z * (D z)⁻¹ * (principalRoot (D z))⁻¹ ∂((μ.prod μ).prod (σ.prod σ))) =
    ((c * Real.sqrt 2 / σ.real univ : ℝ) : ℂ) * ∫ z, diagonalWeight f z * H z.1 ∂((μ.prod μ).prod (σ.prod σ))
  rw [integral_prod _ hi, integral_prod _ hdiag, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [he] with r hr
  rw [hr, hm]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hσ.ne']



set_option maxHeartbeats 1500000 in
private theorem diagonal_half_limit {σ : Measure A} [IsFiniteMeasure σ]
    {f : ℝ × A → ℂ} (hf : Measurable f) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B)
    (hzero : ∀ n, (∫ r, f (r, n) ∂radialMeasure δ) = 0) :
    Tendsto (fun ε : ℝ => ∫ z, diagonalWeight f z *
      (semicircleCapFinitePart (capShift ε z.1.1 z.1.2) - Complex.log (capShift ε z.1.1 z.1.2))
      ∂pairMeasure σ δ) (𝓝[>] 0)
      (𝓝 (-(∫ z, diagonalWeight f z * Complex.log (Complex.I *
        ((2 * (z.1.1 - z.1.2) : ℝ) : ℂ)) ∂pairMeasure σ δ))) := by
  let d (ε : ℝ) (z : Pair A) := capShift ε z.1.1 z.1.2
  let K (d : ℂ) := semicircleCapFinitePart d - Complex.log (2 + d)
  have hK : Tendsto K (𝓝[{d : ℂ | 0 ≤ d.re}] 0) (𝓝 (K 0)) := by
    apply tendsto_semicircleCapFinitePart.sub
    have hc : ContinuousAt (fun d : ℂ => Complex.log (2 + d)) 0 :=
      (continuousAt_const.add continuousAt_id).clog (by simp)
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hmK : Measurable K := by
    unfold K semicircleCapFinitePart halfPowerCapFinitePart
    refine Measurable.sub (Measurable.add ?_ ?_) (Complex.measurable_log.comp (by fun_prop))
    · unfold principalRoot
      fun_prop
    · apply StronglyMeasurable.measurable
      refine StronglyMeasurable.integral_prod_right'
        (ν := (volume : Measure ℝ).restrict (Ioo 0 2))
        (f := fun p : ℂ × ℝ => (densityError p.2 : ℂ) * halfPowerCap p.2 p.1) ?_
      apply Measurable.stronglyMeasurable
      have ht : Measurable (fun t : ℝ => (densityError t : ℂ)) := by
        unfold densityError
        fun_prop
      exact (ht.comp measurable_snd).mul (measurable_halfPowerCap measurable_snd measurable_fst)
  have hd (ε : ℝ) : Measurable (d ε) := by dsimp [d, capShift]; fun_prop
  have hpos (ε : ℝ) {z : Pair A} (hz : z.1.1 ∈ Ioo δ 1 ∧ z.1.2 ∈ Ioo δ 1) :
      0 ≤ (d ε z).re := by
    dsimp only [d]
    rw [capShift_re]
    have hu := hδ.trans hz.1.1
    have hv := hδ.trans hz.2.1
    positivity
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ z ∂pairMeasure σ δ,
      ‖K (d ε z)‖ ≤ ‖K 0‖ + 1 := by
    have hlocal := hK.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1))
    rw [eventually_nhdsWithin_iff] at hlocal
    obtain ⟨ρ, hρ, hr⟩ := Metric.mem_nhds_iff.mp hlocal
    have hs (ε : ℝ) {z : Pair A} (hz : z.1.1 ∈ Ioo δ 1 ∧ z.1.2 ∈ Ioo δ 1)
        (hε : ε ∈ Ioo 0 (min 1 (ρ * δ ^ 2 / 4))) : ‖d ε z‖ < ρ := by
      have hu := hδ.trans hz.1.1
      have hv := hδ.trans hz.2.1
      have hsep : |z.1.1 - z.1.2| ≤ 1 := by
        apply abs_le.mpr
        constructor <;> linarith [hz.1.2, hz.2.2]
      have he₁ : ε ≤ 1 := hε.2.le.trans (min_le_left _ _)
      have he₂ : ε < ρ * δ ^ 2 / 4 := hε.2.trans_le (min_le_right _ _)
      have hp : 0 < 2 * z.1.1 * z.1.2 := by positivity
      have hm : ρ * (δ ^ 2) ≤ ρ * (z.1.1 * z.1.2) := by
        apply mul_le_mul_of_nonneg_left _ hρ.le
        rw [pow_two]
        exact mul_le_mul hz.1.1.le hz.2.1.le hδ.le hu.le
      unfold d capShift
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le]
      apply (div_lt_iff₀ hp).2
      refine (norm_add_le _ _).trans_lt ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg ε),
        abs_of_nonneg (mul_nonneg two_pos.le hε.1.le)]
      nlinarith [mul_le_mul_of_nonneg_left hsep (mul_nonneg two_pos.le hε.1.le),
        mul_le_mul_of_nonneg_left he₁ hε.1.le]
    filter_upwards [Ioo_mem_nhdsGT (show 0 < min 1 (ρ * δ ^ 2 / 4) by positivity)] with ε hε
    filter_upwards [pair_radii_ae σ δ] with z hz
    have hdε : d ε z ∈ Metric.ball (0 : ℂ) ρ := by
      simpa only [Metric.mem_ball, dist_zero_right] using (hs ε hz hε)
    have hh := hr hdε
    change 0 ≤ (d ε z).re → dist (K (d ε z)) (K 0) < 1 at hh
    have h := hh (hpos ε hz)
    have hn : ‖K (d ε z) - K 0‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using h
    exact (norm_le_norm_sub_add (K (d ε z)) (K 0)).trans (by linarith)
  have hlim : Tendsto (fun ε : ℝ => ∫ z, diagonalWeight f z * K (d ε z)
      ∂pairMeasure σ δ) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (μ := pairMeasure σ δ) (F := fun ε z => diagonalWeight f z * K (d ε z))
      (f := fun z => diagonalWeight f z * K 0) (fun _ => B ^ 2 * (‖K 0‖ + 1))
      (.of_forall fun ε => ((diagonalWeight_measurable hf).mul (hmK.comp (hd ε))).aestronglyMeasurable)
      (hsmall.mono fun ε he => by
        filter_upwards [he, diagonalWeight_bound (σ := σ) hB hb] with z hz hz'
        rw [norm_mul]
        gcongr)
      (integrable_const _) (by
        filter_upwards [pair_radii_ae σ δ] with z hz
        have hdz : Tendsto (fun ε => d ε z) (𝓝[>] 0) (𝓝 0) := by
          simpa [d, capShift] using ((continuous_capShift z.1.1 z.1.2).continuousAt
            (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
        exact (hK.comp (tendsto_nhdsWithin_iff.mpr ⟨hdz, .of_forall fun ε => hpos ε hz⟩)).const_mul _)
    rw [integral_mul_const, (diagonalWeight_cancels (σ := σ) hf hδ hB hb hzero).1, zero_mul] at h
    exact h
  have hlog := diagonalCap_boundary (σ := σ) hf hδ hB hb hzero
  have hsum := hlim.add hlog
  rw [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin, hsmall] with ε (hε : 0 < ε) hsmall'
  have hk : Integrable (fun z => diagonalWeight f z * K (d ε z)) (pairMeasure σ δ) := by
    refine (integrable_const (B ^ 2 * (‖K 0‖ + 1))).mono'
      ((diagonalWeight_measurable hf).mul (hmK.comp (hd ε))).aestronglyMeasurable ?_
    filter_upwards [hsmall', diagonalWeight_bound (σ := σ) hB hb] with z hz hz'
    rw [norm_mul]
    gcongr
  have hl : Integrable (fun z => diagonalWeight f z *
      (Complex.log (2 + d ε z) - Complex.log (d ε z))) (pairMeasure σ δ) := by
    let E := ε ^ 2 / 2
    let R := 2 + (ε ^ 2 + 2 * ε) / (2 * δ ^ 2)
    have hE : 0 < E := by dsimp [E]; positivity
    have hR : 0 < R := by dsimp [R]; positivity
    let C := |Real.log E| + |Real.log R| + Real.pi
    refine (integrable_const (B ^ 2 * (C + C))).mono'
      ((diagonalWeight_measurable hf).mul ((Complex.measurable_log.comp
        (measurable_const.add (hd ε))).sub (Complex.measurable_log.comp (hd ε)))).aestronglyMeasurable ?_
    filter_upwards [pair_radii_ae σ δ, diagonalWeight_bound (σ := σ) hB hb] with z hz hb'
    have hu := hδ.trans hz.1.1
    have hv := hδ.trans hz.2.1
    have hp : 0 < 2 * z.1.1 * z.1.2 := by positivity
    have hle : 2 * z.1.1 * z.1.2 ≤ 2 := by
      nlinarith [mul_le_mul hz.1.2.le hz.2.2.le hv.le (show (0 : ℝ) ≤ 1 by norm_num)]
    have hlo : E ≤ (d ε z).re := by
      dsimp only [E, d]
      rw [capShift_re]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hp hle
    have hδle : 2 * δ ^ 2 ≤ 2 * z.1.1 * z.1.2 := by
      nlinarith [mul_le_mul hz.1.1.le hz.2.1.le hδ.le hu.le]
    have hdiff : |z.1.1 - z.1.2| ≤ 1 := by
      apply abs_le.mpr
      constructor <;> linarith [hz.1.2, hz.2.2]
    have hupp : ‖d ε z‖ ≤ R - 2 := by
      dsimp only [R, d, capShift]
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hp.le]
      refine (div_le_div_of_nonneg_right (norm_add_le _ _) hp.le).trans ?_
      rw [add_sub_cancel_left, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ε),
        abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * ε)]
      have hdiff' := mul_le_mul_of_nonneg_left hdiff (mul_nonneg two_pos.le hε.le)
      exact (div_le_div_of_nonneg_right (by nlinarith) hp.le).trans
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hδle)
    have hl₁ : ‖Complex.log (d ε z)‖ ≤ C :=
      norm_log_le_of_modulus_bounds hE (hlo.trans (Complex.re_le_norm _)) (by linarith)
    have hl₂ : ‖Complex.log (2 + d ε z)‖ ≤ C := by
      apply norm_log_le_of_modulus_bounds hE
      · apply le_trans _ (Complex.re_le_norm _)
        simp [Complex.add_re]
        linarith
      · refine (norm_add_le _ _).trans ?_
        simpa using (show 2 + ‖d ε z‖ ≤ R by linarith)
    rw [norm_mul]
    exact mul_le_mul hb' ((norm_sub_le _ _).trans (add_le_add hl₂ hl₁))
      (norm_nonneg _) (sq_nonneg _)
  rw [← integral_add hk hl]
  apply integral_congr_ae
  filter_upwards with z
  unfold K
  ring

/-- The semicircle cap has the angularly diagonal logarithmic boundary on derivative tests. -/
theorem halfCap_boundary {σ : Measure A} [IsFiniteMeasure σ]
    {x : A → A → ℝ} (hx : Measurable (Function.uncurry x)) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ n, Measure.map (x n) σ = (volume.restrict (Icc (-1 : ℝ) 1)).withDensity
      (fun x => ENNReal.ofReal (c * Real.sqrt (1 - x ^ 2))))
    (hupper : ∀ n m, x n m ≤ 1) (hσ : 0 < σ.real univ)
    (hangle : ∀ᵐ p ∂σ.prod σ, x p.1 p.2 < 1)
    (hmajor : Integrable (fun p : A × A => (1 - x p.1 p.2)⁻¹) (σ.prod σ))
    {f : ℝ × A → ℂ} (hf : Measurable f) {δ B C : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B)
    (hlip : ∀ r ∈ Ioo δ 1, ∀ n m, ‖f (r, m) - f (r, n)‖ ≤ C * Real.sqrt (1 - x n m))
    (hzero : ∀ n, (∫ r, f (r, n) ∂radialMeasure δ) = 0) :
    Tendsto (fun ε : ℝ => ∫ z, halfCapIntegrand f x ε z ∂pairMeasure σ δ) (𝓝[>] 0)
      (𝓝 (-((c * Real.sqrt 2 : ℝ) : ℂ) * ∫ n, affineLogIntegral δ f n ∂σ)) := by
  have hr := angularRemainder_half_limit hx hangle hmajor hf hδ hB hb hlip hzero
  have hd := diagonal_half_limit (σ := σ) hf hδ hB hb hzero
  rw [affineLogIntegral_diagonal hf hδ hB hb] at hd
  have hl := hr.add (hd.const_mul ((c * Real.sqrt 2 / σ.real univ : ℝ) : ℂ))
  have he (z : ℂ) :
      0 + ((c * Real.sqrt 2 / σ.real univ : ℝ) : ℂ) * (-((σ.real univ : ℂ) * z)) =
        -((c * Real.sqrt 2 : ℝ) : ℂ) * z := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hσ.ne']
    <;> ring
  rw [he] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (halfCapIntegrand_split hx hc hcap hf hδ hB hε hb hupper hσ).symm

end Omega.ConeCap
