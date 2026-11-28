/- GID: D5/S3/Analysis/ConeCapLimits
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-weak-boundary4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The angular subtraction and radial logarithm in regulated cone cap pairings. -/

import OmegaBuild.Commands
import D5.S3.Analysis.RightHalfPlaneLogIntegral
import Mathlib.MeasureTheory.Integral.Prod

/-!
Omega original.

The angular subtraction and radial logarithm in regulated cone cap pairings.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Topology ENNReal NNReal

namespace Omega

namespace ConeCap

/-- Lebesgue measure restricted to the interior radial interval above a cutoff. -/
def radialMeasure (δ : ℝ) : Measure ℝ := volume.restrict (Ioo δ 1)

local instance (δ : ℝ) : IsFiniteMeasure (radialMeasure δ) := by
  unfold radialMeasure
  infer_instance

abbrev Pair (A : Type*) := (ℝ × ℝ) × (A × A)

/-- The pair measure with the radial coordinates first. -/
def pairMeasure {A : Type*} [MeasurableSpace A] (σ : Measure A) (δ : ℝ) :
    Measure (Pair A) :=
  ((radialMeasure δ).prod (radialMeasure δ)).prod (σ.prod σ)

private local instance {A : Type*} [MeasurableSpace A] (σ : Measure A)
    [IsFiniteMeasure σ] (δ : ℝ) : IsFiniteMeasure (pairMeasure σ δ) := by
  unfold pairMeasure
  infer_instance

variable {A : Type*} [MeasurableSpace A]

private theorem pair_radii_ae (σ : Measure A) [IsFiniteMeasure σ] (δ : ℝ) :
    ∀ᵐ z ∂pairMeasure σ δ, z.1.1 ∈ Ioo δ 1 ∧ z.1.2 ∈ Ioo δ 1 := by
  let μ := radialMeasure δ
  have h : ∀ᵐ u ∂μ, u ∈ Ioo δ 1 := ae_restrict_mem measurableSet_Ioo
  exact (((μ.prod μ).quasiMeasurePreserving_fst (ν := σ.prod σ)).ae
    (((μ.quasiMeasurePreserving_fst (ν := μ)).ae h).and
      ((μ.quasiMeasurePreserving_snd (μ := μ)).ae h)))

private theorem capped_angle_ae {σ : Measure A} [IsFiniteMeasure σ] {x : A → A → ℝ}
    (hx : Measurable (Function.uncurry x)) {c : ℝ}
    (hcap : ∀ n, Measure.map (x n) σ = ENNReal.ofReal c • volume.restrict (Icc (-1 : ℝ) 1)) :
    ∀ᵐ m ∂σ.prod σ, x m.1 m.2 < 1 := by
  apply (ae_prod_iff_ae_ae (measurableSet_lt hx measurable_const)).mpr
  exact .of_forall fun n => by
    have h : Measurable (x n) := hx.comp (measurable_const.prodMk measurable_id)
    rw [ae_iff]
    simp only [not_lt]
    change σ (x n ⁻¹' Ici (1 : ℝ)) = 0
    rw [← Measure.map_apply h measurableSet_Ici, hcap n, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Ici]
    have he : Ici (1 : ℝ) ∩ Icc (-1 : ℝ) 1 = {1} := by
      ext t
      simp only [mem_inter_iff, mem_Icc, mem_Ici, mem_singleton_iff]
      constructor
      · exact fun h => le_antisymm h.2.2 h.1
      · rintro rfl
        norm_num
    rw [he, measure_singleton, smul_zero]

private theorem angular_majorant {σ : Measure A} [IsFiniteMeasure σ] {x : A → A → ℝ}
    (hx : Measurable (Function.uncurry x)) {c : ℝ}
    (hcap : ∀ n, Measure.map (x n) σ = ENNReal.ofReal c • volume.restrict (Icc (-1 : ℝ) 1)) :
    Integrable (fun p : A × A => (Real.sqrt (1 - x p.1 p.2))⁻¹) (σ.prod σ) := by
  let g : ℝ → ℝ := fun z => (Real.sqrt (1-z))⁻¹
  have hm : Measurable g := by dsimp [g]; fun_prop
  have hp : Measurable (fun p : A × A => (Real.sqrt (1 - x p.1 p.2))⁻¹) :=
    hm.comp hx
  refine (integrable_prod_iff hp.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact .of_forall fun n =>
      integrable_inv_sqrt_mapped_cap (hx.comp (measurable_const.prodMk measurable_id)) (hcap n)
  · have he (n : A) :
        (∫ m, ‖(Real.sqrt (1 - x n m))⁻¹‖ ∂σ) =
          ∫ z, g z ∂(ENNReal.ofReal c • volume.restrict (Icc (-1 : ℝ) 1)) := by
      have h : Measurable (x n) := hx.comp (measurable_const.prodMk measurable_id)
      simp_rw [Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      change (∫ m, g (x n m) ∂σ) = _
      rw [← integral_map h.aemeasurable hm.aestronglyMeasurable, hcap n]
    simpa only [he] using integrable_const
      (μ := σ) (∫ z, g z ∂(ENNReal.ofReal c • volume.restrict (Icc (-1 : ℝ) 1)))

def first {A : Type*} (z : Pair A) : ℝ × A := (z.1.1, z.2.1)
def second {A : Type*} (z : Pair A) : ℝ × A := (z.1.2, z.2.2)
private def coincident {A : Type*} (z : Pair A) : ℝ × A := (z.1.2, z.2.1)

private theorem first_measurable : Measurable (first (A := A)) :=
  (measurable_fst.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)

private theorem second_measurable : Measurable (second (A := A)) :=
  (measurable_snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)

private theorem coincident_measurable : Measurable (coincident (A := A)) :=
  (measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd)

private def angularRemainder (f : ℝ × A → ℂ) (z : Pair A) : ℂ :=
  star (f (first z)) * (f (second z) - f (coincident z))

private theorem angularRemainder_measurable {f : ℝ × A → ℂ} (hf : Measurable f) :
    Measurable (angularRemainder f) :=
  (show Measurable (fun z => star (f (first z))) from
    Complex.continuous_conj.measurable.comp (hf.comp first_measurable)).mul
    ((hf.comp second_measurable).sub (hf.comp coincident_measurable))

set_option maxHeartbeats 1000000 in
-- Elaborating the product measures and the dominated-convergence data uses a larger budget.
/-- Dominated convergence of the part with the coincident angular value subtracted. -/
private theorem angularRemainder_boundary {σ : Measure A} [IsFiniteMeasure σ]
    {x : A → A → ℝ} (hx : Measurable (Function.uncurry x))
    {c : ℝ}
    (hcap : ∀ n, Measure.map (x n) σ = ENNReal.ofReal c • volume.restrict (Icc (-1 : ℝ) 1))
    {f : ℝ × A → ℂ} (hf : Measurable f) {δ B C : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B)
    (hc : ∀ r ∈ Ioo δ 1, ∀ n m, ‖f (r, m) - f (r, n)‖ ≤ C * Real.sqrt (1 - x n m)) :
    Tendsto (fun ε : ℝ => ∫ z, angularRemainder f z /
      ((1 - x z.2.1 z.2.2 : ℝ) + capShift ε z.1.1 z.1.2) ∂pairMeasure σ δ)
      (𝓝[>] 0) (𝓝 (∫ z, angularRemainder f z /
        ((1 - x z.2.1 z.2.2 : ℝ) : ℂ) ∂pairMeasure σ δ)) := by
  have hpos : ∀ᵐ z ∂pairMeasure σ δ, 0 < 1 - x z.2.1 z.2.2 :=
    ((σ.prod σ).quasiMeasurePreserving_snd
      (μ := (radialMeasure δ).prod (radialMeasure δ))).ae
        ((capped_angle_ae hx hcap).mono fun _ h => sub_pos.mpr h)
  let r : Pair A → ℝ := fun z => 1 - x z.2.1 z.2.2
  let d : ℝ → Pair A → ℂ := fun ε z => capShift ε z.1.1 z.1.2
  have hr : Measurable r := (measurable_const.sub hx).comp measurable_snd
  have hd (ε : ℝ) : Measurable (d ε) := by
    dsimp [d, capShift]
    fun_prop
  have hbound : ∀ᵐ z ∂pairMeasure σ δ, ‖angularRemainder f z‖ ≤ (B * C) * Real.sqrt (r z) := by
    filter_upwards [pair_radii_ae σ δ] with z hz
    rw [angularRemainder, norm_mul, norm_star]
    exact (mul_le_mul (hb _ hz.1 _) (hc _ hz.2 _ _) (norm_nonneg _) hB).trans_eq
      (mul_assoc _ _ _).symm
  have hi : Integrable (fun z => (Real.sqrt (r z))⁻¹) (pairMeasure σ δ) :=
    ((integrable_const (μ := (radialMeasure δ).prod (radialMeasure δ)) (1 : ℝ))
      |>.mul_prod (angular_majorant hx hcap)).congr
      (.of_forall fun z => one_mul _)
  have hre : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, ∀ᵐ z ∂pairMeasure σ δ, 0 ≤ (d ε z).re :=
    .of_forall fun ε => (pair_radii_ae σ δ).mono fun z hz => by
      dsimp only [d]
      rw [capShift_re]
      have hu := hδ.trans hz.1.1
      have hv := hδ.trans hz.2.1
      positivity
  have hlim : ∀ᵐ z ∂pairMeasure σ δ, Tendsto (fun ε => d ε z) (𝓝[>] 0) (𝓝 0) :=
    .of_forall fun z => by
      simpa using ((continuous_capShift z.1.1 z.1.2).continuousAt (x := (0 : ℝ))).tendsto
        |>.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  exact tendsto_integral_div_add_of_sqrt_bound (r := r) (d := d) hr
    (angularRemainder_measurable hf).aestronglyMeasurable hd
    (mul_nonneg hB hC) hpos hbound hi hre hlim

private def diagonalWeight (f : ℝ × A → ℂ) (z : Pair A) : ℂ :=
  star (f (first z)) * f (coincident z)

private theorem diagonalWeight_measurable {f : ℝ × A → ℂ} (hf : Measurable f) :
    Measurable (diagonalWeight f) :=
  (Complex.continuous_conj.measurable.comp (hf.comp first_measurable)).mul
    (hf.comp coincident_measurable)

private theorem radialDiagonal_ae (δ : ℝ) :
    ∀ᵐ p ∂(radialMeasure δ).prod (radialMeasure δ), p.1 ≠ p.2 := by
  apply (ae_prod_iff_ae_ae ((measurableSet_eq_fun measurable_fst measurable_snd).compl)).mpr
  exact .of_forall fun u => by
    have h : ∀ᵐ v ∂radialMeasure δ, v ≠ u := (ae_restrict_le (ae_ne volume u))
    exact h.mono fun _ hv => Ne.symm hv

private theorem integrable_radial_log {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun p : ℝ × ℝ => |Real.log (|2 * (p.1 - p.2)|)|)
      ((radialMeasure δ).prod (radialMeasure δ)) := by
  have h : radialMeasure δ ≤ radialMeasure 0 := by
    unfold radialMeasure
    exact Measure.restrict_mono (Ioo_subset_Ioo_left hδ.le) le_rfl
  exact integrable_log_difference_unit.mono_measure (Measure.prod_mono h h)

private theorem diagonalWeight_bound {σ : Measure A} [IsFiniteMeasure σ]
    {f : ℝ × A → ℂ} {δ B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B) :
    ∀ᵐ z ∂pairMeasure σ δ, ‖diagonalWeight f z‖ ≤ B ^ 2 := by
  filter_upwards [pair_radii_ae σ δ] with z hz
  rw [diagonalWeight, norm_mul, norm_star, pow_two]
  exact mul_le_mul (hb _ hz.1 _) (hb _ hz.2 _) (norm_nonneg _) hB

private theorem diagonalWeight_cancels {σ : Measure A} [IsFiniteMeasure σ]
    {f : ℝ × A → ℂ} (hf : Measurable f)
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B)
    (hzero : ∀ n, (∫ r, f (r, n) ∂radialMeasure δ) = 0) :
    (∫ z, diagonalWeight f z ∂pairMeasure σ δ) = 0 ∧
    (∫ z, diagonalWeight f z * (Real.log z.1.1 : ℂ) ∂pairMeasure σ δ) = 0 ∧
    (∫ z, diagonalWeight f z * (Real.log z.1.2 : ℂ) ∂pairMeasure σ δ) = 0 := by
  let μ := radialMeasure δ
  let P : (ℝ × A → ℂ) → (ℝ × A → ℂ) → Pair A → ℂ :=
    fun g h z => star (g (first z)) * h (coincident z)
  have eval (g h : ℝ × A → ℂ) (hi : Integrable (P g h) (pairMeasure σ δ)) :
      (∫ z, P g h z ∂pairMeasure σ δ) =
        ∫ p : A × A, star (∫ r, g (r, p.1) ∂μ) * (∫ r, h (r, p.1) ∂μ) ∂(σ.prod σ) := by
    rw [pairMeasure, integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards with p
    dsimp [P, first, coincident]
    simpa only [Complex.star_def, integral_conj] using
      (integral_prod_mul (μ := μ) (ν := μ) (fun r => star (g (r, p.1))) (fun r => h (r, p.1)))
  let g : ℝ × A → ℂ := fun p => f p * (Real.log p.1 : ℂ)
  have hg : Measurable g := hf.mul
    (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp measurable_fst))
  have H (j k : ℝ × A → ℂ) (hj : Measurable j) (hk : Measurable k)
      {J K : ℝ} (hjB : 0 ≤ J)
      (hj' : ∀ r ∈ Ioo δ 1, ∀ n, ‖j (r,n)‖ ≤ J)
      (hk' : ∀ r ∈ Ioo δ 1, ∀ n, ‖k (r,n)‖ ≤ K) :
      Integrable (P j k) (pairMeasure σ δ) := by
    refine (integrable_const (J * K)).mono'
      ((Complex.continuous_conj.measurable.comp (hj.comp first_measurable)).mul
        (hk.comp coincident_measurable)).aestronglyMeasurable ?_
    filter_upwards [pair_radii_ae σ δ] with z hz
    exact (norm_mul _ _).trans_le (by
      rw [norm_star]
      exact mul_le_mul (hj' _ hz.1 _) (hk' _ hz.2 _) (norm_nonneg _) hjB)
  have hg' (r : ℝ) (hr : r ∈ Ioo δ 1) (n : A) : ‖g (r,n)‖ ≤ B * |Real.log δ| := by
    dsimp [g]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul (hb r hr n) ?_ (abs_nonneg _) hB
    rw [abs_of_nonpos (Real.log_nonpos (hδ.trans hr.1).le hr.2.le),
      abs_of_nonpos (Real.log_nonpos hδ.le (hr.1.trans hr.2).le)]
    exact neg_le_neg (Real.log_le_log hδ hr.1.le)
  have eu : (fun z => diagonalWeight f z * (Real.log z.1.1 : ℂ)) = P g f := by
    funext z
    simp only [diagonalWeight, P, g, first, Complex.star_def, map_mul, Complex.conj_ofReal]
    ring
  have ev : (fun z => diagonalWeight f z * (Real.log z.1.2 : ℂ)) = P f g := by
    funext z
    simp only [diagonalWeight, P, g, coincident]
    ring
  refine ⟨?_, ?_, ?_⟩
  · change (∫ z, P f f z ∂pairMeasure σ δ) = 0
    rw [eval f f (H f f hf hf hB hb hb)]
    simp [hzero, μ]
  · rw [eu, eval g f (H g f hg hf (by positivity) hg' hb)]
    simp [hzero, μ]
  · rw [ev, eval f g (H f g hf hg hB hb hg')]
    simp [hzero, μ]

/-- Pairing the logarithmic cap primitive with mean-zero radial derivatives
leaves the diagonal affine boundary logarithm. -/
private theorem diagonalCap_boundary {σ : Measure A} [IsFiniteMeasure σ]
    {f : ℝ × A → ℂ} (hf : Measurable f) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B)
    (hzero : ∀ n, (∫ r, f (r, n) ∂radialMeasure δ) = 0) :
    Tendsto (fun ε : ℝ => ∫ z, diagonalWeight f z *
      (Complex.log (2 + capShift ε z.1.1 z.1.2) - Complex.log (capShift ε z.1.1 z.1.2))
      ∂pairMeasure σ δ) (𝓝[>] 0)
      (𝓝 (-(∫ z, diagonalWeight f z * Complex.log (Complex.I *
        ((2 * (z.1.1 - z.1.2) : ℝ) : ℂ)) ∂pairMeasure σ δ))) := by
  let μ := radialMeasure δ
  obtain ⟨h₀, h₁, h₂⟩ := diagonalWeight_cancels (σ := σ) hf hδ hB hb hzero
  have hb' : ∀ᵐ z ∂pairMeasure σ δ,
      δ ≤ z.1.1 ∧ z.1.1 ≤ 1 ∧ δ ≤ z.1.2 ∧ z.1.2 ≤ 1 ∧ ‖diagonalWeight f z‖ ≤ B ^ 2 := by
    filter_upwards [pair_radii_ae σ δ, diagonalWeight_bound (σ := σ) hB hb] with z hz hn
    exact ⟨hz.1.1.le, hz.1.2.le, hz.2.1.le, hz.2.2.le, hn⟩
  have hn : ∀ᵐ z ∂pairMeasure σ δ, z.1.1 ≠ z.1.2 :=
    ((μ.prod μ).quasiMeasurePreserving_fst (ν := σ.prod σ)).ae (radialDiagonal_ae δ)
  have hlog : Integrable (fun z : Pair A => |Real.log (|2 * (z.1.1 - z.1.2)|)|)
      (pairMeasure σ δ) := (integrable_radial_log hδ).comp_fst (σ.prod σ)
  exact tendsto_integral_cap_logs (measurable_fst.comp measurable_fst)
    (measurable_snd.comp measurable_fst) (diagonalWeight_measurable hf).aestronglyMeasurable
    hδ (sq_nonneg B) hb' hn hlog h₀ h₁ h₂

private theorem angularRemainder_integral_eq_zero {σ : Measure A} [IsFiniteMeasure σ]
    {x : A → A → ℝ} (hx : Measurable (Function.uncurry x)) {c : ℝ}
    (hcap : ∀ n, Measure.map (x n) σ = ENNReal.ofReal c • volume.restrict (Icc (-1 : ℝ) 1))
    {f : ℝ × A → ℂ} (hf : Measurable f) {δ B C : ℝ} (hB : 0 ≤ B)
    (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B)
    (hc : ∀ r ∈ Ioo δ 1, ∀ n m, ‖f (r, m) - f (r, n)‖ ≤ C * Real.sqrt (1 - x n m))
    (hzero : ∀ n, (∫ r, f (r, n) ∂radialMeasure δ) = 0) :
    (∫ z, angularRemainder f z / ((1 - x z.2.1 z.2.2 : ℝ) : ℂ) ∂pairMeasure σ δ) = 0 := by
  let R : (A × A) → ℝ := fun z => 1 - x z.1 z.2
  let μ := radialMeasure δ
  let g : Pair A → ℂ := fun z => angularRemainder f z / (R z.2 : ℂ)
  have hg : Measurable g := (angularRemainder_measurable hf).div
    (Complex.continuous_ofReal.measurable.comp ((measurable_const.sub hx).comp measurable_snd))
  have hpos : ∀ᵐ z ∂pairMeasure σ δ, 0 < R z.2 :=
    ((σ.prod σ).quasiMeasurePreserving_snd (μ := μ.prod μ)).ae
      ((capped_angle_ae hx hcap).mono fun _ h => sub_pos.mpr h)
  have hi : Integrable g (pairMeasure σ δ) := by
    apply (((angular_majorant hx hcap).comp_snd (μ.prod μ)).const_mul (B * C)).mono'
      hg.aestronglyMeasurable
    filter_upwards [pair_radii_ae σ δ, hpos] with z hz hr
    have ha := mul_le_mul (hb _ hz.1 z.2.1) (hc _ hz.2 z.2.1 z.2.2) (norm_nonneg _) hB
    dsimp only [g, angularRemainder]
    rw [norm_div, norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg hr.le]
    calc
      _ ≤ (B * (C * Real.sqrt (R z.2))) / R z.2 :=
        div_le_div_of_nonneg_right ha hr.le
      _ = (B * C * Real.sqrt (R z.2)) / (Real.sqrt (R z.2)) ^ 2 := by
        rw [Real.sq_sqrt hr.le]
        unfold R
        ring
      _ = _ := by
        change _ = B * C * (Real.sqrt (R z.2))⁻¹
        field_simp [(Real.sqrt_pos.2 hr).ne']
  change (∫ z, g z ∂((μ.prod μ).prod (σ.prod σ))) = 0
  rw [integral_prod_symm _ hi]
  apply integral_eq_zero_of_ae
  filter_upwards with p
  change (∫ r : ℝ × ℝ, (star (f (r.1, p.1)) * (f (r.2, p.2) - f (r.2, p.1))) /
    (R p : ℂ) ∂(μ.prod μ)) = 0
  simp_rw [div_eq_mul_inv, integral_mul_const]
  rw [integral_prod_mul (fun r => star (f (r, p.1))) (fun r => f (r, p.2) - f (r, p.1))]
  dsimp only [Complex.star_def]
  rw [integral_conj, hzero p.1, map_zero, zero_mul, zero_mul]

/-- The regulated angular denominator paired with the radial test derivatives. -/
def capIntegrand (f : ℝ × A → ℂ) (x : A → A → ℝ) (ε : ℝ) (z : Pair A) : ℂ :=
  star (f (first z)) * f (second z) /
    ((1 - x z.2.1 z.2.2 : ℝ) + capShift ε z.1.1 z.1.2)

set_option maxHeartbeats 1500000 in
-- The product-measure Fubini steps require a larger elaboration budget.
private theorem capIntegrand_split {σ : Measure A} [IsFiniteMeasure σ]
    {x : A → A → ℝ} (hx : Measurable (Function.uncurry x)) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ n, Measure.map (x n) σ = ENNReal.ofReal c • volume.restrict (Icc (-1 : ℝ) 1))
    {f : ℝ × A → ℂ} (hf : Measurable f) {δ B ε : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hε : 0 < ε) (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B)
    (hupper : ∀ n m, x n m ≤ 1) (hσ : 0 < σ.real univ) :
    (∫ z, capIntegrand f x ε z ∂pairMeasure σ δ) =
      (∫ z, angularRemainder f z /
        ((1 - x z.2.1 z.2.2 : ℝ) + capShift ε z.1.1 z.1.2) ∂pairMeasure σ δ) +
      ((c / σ.real univ : ℝ) : ℂ) * (∫ z, diagonalWeight f z *
        (Complex.log (2 + capShift ε z.1.1 z.1.2) - Complex.log (capShift ε z.1.1 z.1.2))
        ∂pairMeasure σ δ) := by
  let μ := radialMeasure δ
  let D : Pair A → ℂ := fun z =>
    (1 - x z.2.1 z.2.2 : ℝ) + capShift ε z.1.1 z.1.2
  let H : ℝ × ℝ → ℂ := fun r =>
    Complex.log (2 + capShift ε r.1 r.2) - Complex.log (capShift ε r.1 r.2)
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
      Integrable (fun z => g z / D z) (pairMeasure σ δ) := by
    have hp : 0 < ε ^ 2 / 2 := by positivity
    apply (integrable_const (C / (ε ^ 2 / 2))).mono' (hg.div hD).aestronglyMeasurable
    filter_upwards [hnorm, hC] with z hz hb'
    rw [Pi.div_apply, norm_div]
    exact (div_le_div_of_nonneg_left (norm_nonneg _) hp hz).trans
      (div_le_div_of_nonneg_right hb' hp.le)
  have hi := bound (diagonalWeight f) (diagonalWeight_measurable hf) (diagonalWeight_bound hB hb)
  have hj : Integrable (fun z => angularRemainder f z / D z) (pairMeasure σ δ) := by
    apply bound _ (angularRemainder_measurable hf) (C := B * (B + B))
    filter_upwards [pair_radii_ae σ δ] with z hz
    rw [angularRemainder, norm_mul, norm_star]
    exact mul_le_mul (hb _ hz.1 _) ((norm_sub_le _ _).trans (add_le_add (hb _ hz.2 _) (hb _ hz.2 _)))
      (norm_nonneg _) hB
  have hsplit : capIntegrand f x ε = fun z =>
      angularRemainder f z / D z + diagonalWeight f z / D z := by
    funext z
    dsimp only [capIntegrand, angularRemainder, diagonalWeight, D]
    rw [← add_div, ← mul_add, sub_add_cancel]
  rw [hsplit, integral_add hj hi, _root_.add_right_inj]
  have he : ∀ᵐ r ∂μ.prod μ,
      (∫ p : A × A, diagonalWeight f (r, p) / D (r, p) ∂σ.prod σ) =
      (c : ℂ) * (∫ n, star (f (r.1, n)) * f (r.2, n) ∂σ) * H r := by
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
    have hcap' (n : A) := mapped_cap_integral
      (x := x n) (hx.comp (measurable_const.prodMk measurable_id)) hc.le (hcap n) hd
    have hinner (n : A) :
        (∫ m, diagonalWeight f (r, n, m) / D (r, n, m) ∂σ) =
          ((c : ℂ) * H r) * (star (f (r.1, n)) * f (r.2, n)) := by
      simp only [D, diagonalWeight, first, coincident, div_eq_mul_inv, integral_const_mul]
      push_cast
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
    have hp : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    have heq : (fun z => diagonalWeight f z * H z.1) =ᵐ[pairMeasure σ δ]
        fun z => (c : ℂ)⁻¹ * (∫ m, diagonalWeight f (z.1, z.2.1, m) /
          D (z.1, z.2.1, m) ∂σ) := by
      filter_upwards [pair_radii_ae σ δ] with z hz
      have hd : 0 < (capShift ε z.1.1 z.1.2).re := by
        rw [capShift_re]
        have hu := hδ.trans hz.1.1
        have hv := hδ.trans hz.2.1
        positivity
      have ht := mapped_cap_integral (x := x z.2.1) (hx.comp (measurable_const.prodMk measurable_id))
        hc.le (hcap z.2.1) hd
      simp only [D, diagonalWeight, first, coincident, div_eq_mul_inv, integral_const_mul]
      push_cast
      rw [ht]
      dsimp [H]
      field_simp [hp]
    have ha : Integrable (fun p : ((ℝ × ℝ) × A) × A =>
        diagonalWeight f (p.1.1, p.1.2, p.2) / D (p.1.1, p.1.2, p.2))
        (((μ.prod μ).prod σ).prod σ) :=
      (measurePreserving_prodAssoc (μ.prod μ) σ σ).integrable_comp_of_integrable hi
    have hfirst := (ha.integral_prod_left.const_mul (c : ℂ)⁻¹).comp_fst σ
    have hb' := ((measurePreserving_prodAssoc (μ.prod μ) σ σ).symm
      MeasurableEquiv.prodAssoc).integrable_comp_of_integrable hfirst
    exact hb'.congr heq.symm
  change (∫ z, diagonalWeight f z / D z ∂((μ.prod μ).prod (σ.prod σ))) =
    ((c / σ.real univ : ℝ) : ℂ) * ∫ z, diagonalWeight f z * H z.1 ∂((μ.prod μ).prod (σ.prod σ))
  rw [integral_prod _ hi, integral_prod _ hdiag, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [he] with r hr
  rw [hr, hm]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hσ.ne']

/-- The diagonal logarithm after the radial and angular variables have been separated. -/
def affineLogIntegral (δ : ℝ) (f : ℝ × A → ℂ) (n : A) : ℂ :=
  ∫ r : ℝ × ℝ, star (f (r.1, n)) * f (r.2, n) *
    Complex.log (Complex.I * ((2 * (r.1 - r.2) : ℝ) : ℂ))
    ∂((radialMeasure δ).prod (radialMeasure δ))

private theorem affineLogIntegral_diagonal {σ : Measure A} [IsFiniteMeasure σ]
    {f : ℝ × A → ℂ} (hf : Measurable f) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B) :
    (∫ z, diagonalWeight f z * Complex.log (Complex.I *
        ((2 * (z.1.1 - z.1.2) : ℝ) : ℂ)) ∂pairMeasure σ δ) =
      (σ.real univ : ℂ) * ∫ n, affineLogIntegral δ f n ∂σ := by
  let μ := radialMeasure δ
  let L : ℝ × ℝ → ℂ := fun r => Complex.log (Complex.I * ((2 * (r.1 - r.2) : ℝ) : ℂ))
  have hL : Measurable L := by dsimp [L]; fun_prop
  have hnorm (r : ℝ × ℝ) :
      ‖L r‖ ≤ |Real.log (|2 * (r.1 - r.2)|)| + Real.pi := by
    have hh := (norm_add_le _ _ :
        ‖(Real.log ‖Complex.I * ((2 * (r.1 - r.2) : ℝ) : ℂ)‖ : ℂ) +
          (Complex.arg (Complex.I * ((2 * (r.1 - r.2) : ℝ) : ℂ)) : ℂ) * Complex.I‖ ≤ _)
    rw [← Complex.log] at hh
    refine hh.trans ?_
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, one_mul, mul_one, abs_mul]
    exact add_le_add_right
      (abs_le.mpr ⟨(Complex.neg_pi_lt_arg (Complex.I * ((2 * (r.1 - r.2) : ℝ) : ℂ))).le,
        Complex.arg_le_pi (Complex.I * ((2 * (r.1 - r.2) : ℝ) : ℂ))⟩)
      |Real.log (|2| * |r.1 - r.2|)|
  have hi : Integrable (fun z => diagonalWeight f z * L z.1) (pairMeasure σ δ) := by
    refine ((((integrable_radial_log hδ).add (integrable_const Real.pi)).comp_fst
      (σ.prod σ)).const_mul (B ^ 2)).mono'
        ((diagonalWeight_measurable hf).mul (hL.comp measurable_fst)).aestronglyMeasurable ?_
    filter_upwards [diagonalWeight_bound (σ := σ) hB hb] with z hz
    rw [norm_mul]
    exact mul_le_mul hz (hnorm z.1) (norm_nonneg _) (sq_nonneg B)
  change (∫ z, _ ∂((μ.prod μ).prod (σ.prod σ))) = _
  rw [integral_prod_symm _ hi]
  change (∫ p : A × A, affineLogIntegral δ f p.1 ∂σ.prod σ) = _
  rw [integral_fun_fst, Complex.real_smul]

/-- The normalized cap boundary has only the coincident-angle logarithmic term.
The angular remainder integrates to zero by the radial mean-zero condition. -/
theorem cap_boundary {σ : Measure A} [IsFiniteMeasure σ]
    {x : A → A → ℝ} (hx : Measurable (Function.uncurry x)) {c : ℝ} (hc : 0 < c)
    (hcap : ∀ n, Measure.map (x n) σ = ENNReal.ofReal c • volume.restrict (Icc (-1 : ℝ) 1))
    (hupper : ∀ n m, x n m ≤ 1) (hσ : 0 < σ.real univ)
    {f : ℝ × A → ℂ} (hf : Measurable f) {δ B C : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ r ∈ Ioo δ 1, ∀ n, ‖f (r, n)‖ ≤ B)
    (hlip : ∀ r ∈ Ioo δ 1, ∀ n m, ‖f (r, m) - f (r, n)‖ ≤ C * Real.sqrt (1 - x n m))
    (hzero : ∀ n, (∫ r, f (r, n) ∂radialMeasure δ) = 0) :
    Tendsto (fun ε : ℝ => ∫ z, capIntegrand f x ε z ∂pairMeasure σ δ) (𝓝[>] 0)
      (𝓝 (-(c : ℂ) * ∫ n, affineLogIntegral δ f n ∂σ)) := by
  have hr := angularRemainder_boundary hx hcap hf hδ hB hC hb hlip
  have hz := angularRemainder_integral_eq_zero hx hcap hf hB hb hlip hzero
  rw [hz] at hr
  have hd := diagonalCap_boundary (σ := σ) hf hδ hB hb hzero
  rw [affineLogIntegral_diagonal hf hδ hB hb] at hd
  have hl := hr.add (hd.const_mul ((c / σ.real univ : ℝ) : ℂ))
  have he (z : ℂ) :
      0 + ((c / σ.real univ : ℝ) : ℂ) * (-((σ.real univ : ℂ) * z)) =
        -(c : ℂ) * z := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hσ.ne']
    exact zero_add _
  rw [he] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (capIntegrand_split hx hc hcap hf hδ hB hε hb hupper hσ).symm

/-- A radial cut can be inserted if the test is zero below that cut. -/
theorem integral_radial_cut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} (hδ : 0 ≤ δ) (g : ℝ → E)
    (hg : ∀ u ∈ Ioo (0 : ℝ) 1, u ≤ δ → g u = 0) :
    (∫ u, g u ∂radialMeasure (0 : ℝ)) = ∫ u, g u ∂radialMeasure δ := by
  unfold radialMeasure
  rw [← integral_indicator measurableSet_Ioo, ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Ioo δ 1
  · rw [indicator_of_mem (Ioo_subset_Ioo_left hδ hu), indicator_of_mem hu]
  · rw [indicator_of_notMem hu]
    by_cases h : u ∈ Ioo (0 : ℝ) 1
    · rw [indicator_of_mem h, hg u h (le_of_not_gt fun hd => hu ⟨hd, h.2⟩)]
    · exact indicator_of_notMem h _

/-- The same radial cut may be inserted in both factors of a product integral. -/
theorem integral_radial_pair_cut {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {δ : ℝ} (hδ : 0 ≤ δ) (g : ℝ × ℝ → E)
    (hg : ∀ r ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1, (r.1 ≤ δ ∨ r.2 ≤ δ) → g r = 0) :
    (∫ r, g r ∂(radialMeasure (0 : ℝ)).prod (radialMeasure (0 : ℝ))) =
      ∫ r, g r ∂(radialMeasure δ).prod (radialMeasure δ) := by
  unfold radialMeasure
  rw [Measure.prod_restrict, Measure.prod_restrict,
    ← integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo),
    ← integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  apply integral_congr_ae
  filter_upwards with r
  let s := Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1
  let t := Ioo δ 1 ×ˢ Ioo δ 1
  have ht : t ⊆ s := prod_mono (Ioo_subset_Ioo_left hδ) (Ioo_subset_Ioo_left hδ)
  by_cases hr : r ∈ t
  · rw [indicator_of_mem (ht hr), indicator_of_mem hr]
  · rw [indicator_of_notMem hr]
    by_cases h : r ∈ s
    · rw [indicator_of_mem h]
      apply hg r h
      by_contra! ha
      exact hr ⟨⟨ha.1, h.1.2⟩, ⟨ha.2, h.2.2⟩⟩
    · exact indicator_of_notMem h _

/-- Cut both radii while retaining the angular product. -/
theorem integral_cap_pair_cut {σ : Measure A} [IsFiniteMeasure σ]
    {δ : ℝ} (hδ : 0 ≤ δ) (g : Pair A → ℂ)
    (hg : ∀ z : Pair A, z.1 ∈ Ioo (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) 1 →
      (z.1.1 ≤ δ ∨ z.1.2 ≤ δ) → g z = 0) :
    (∫ z, g z ∂pairMeasure σ 0) = ∫ z, g z ∂pairMeasure σ δ := by
  let ρ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod (volume : Measure ℝ)
  let S (a : ℝ) := Ioo a 1 ×ˢ Ioo a 1
  have hp (a : ℝ) : pairMeasure σ a =
      (ρ.prod (σ.prod σ)).restrict (S a ×ˢ univ) := by
    unfold pairMeasure radialMeasure S ρ
    rw [← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ]
  have hm (a : ℝ) : MeasurableSet (S a ×ˢ (univ : Set (A × A))) :=
    (measurableSet_Ioo.prod measurableSet_Ioo).prod MeasurableSet.univ
  rw [hp 0, hp δ, ← integral_indicator (hm 0), ← integral_indicator (hm δ)]
  apply integral_congr_ae
  filter_upwards with z
  have ht : S δ ×ˢ (univ : Set (A × A)) ⊆ S 0 ×ˢ univ :=
    prod_mono (prod_mono (Ioo_subset_Ioo_left hδ) (Ioo_subset_Ioo_left hδ)) le_rfl
  by_cases hz : z ∈ S δ ×ˢ (univ : Set (A × A))
  · rw [indicator_of_mem (ht hz), indicator_of_mem hz]
  · rw [indicator_of_notMem hz]
    by_cases h : z ∈ S 0 ×ˢ (univ : Set (A × A))
    · rw [indicator_of_mem h]
      apply hg z h.1
      by_contra! ha
      exact hz ⟨⟨⟨ha.1, h.1.1.2⟩, ⟨ha.2, h.1.2.2⟩⟩, h.2⟩
    · exact indicator_of_notMem h _

/-- Finite sums of separated tests have uniform angular Lipschitz constants
on a compact radial set. -/
theorem separated_sum_angular_bound {A : Type*} [PseudoMetricSpace A] {T : Type*}
    (terms : List T) {S : Set ℝ} (hS : IsCompact S)
    (radial : T → ℝ → ℂ) (angular : T → A → ℂ)
    (hr : ∀ t, Continuous (radial t)) (ha : ∀ t, ∃ K : ℝ≥0, LipschitzWith K (angular t)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ S, ∀ n m,
      ‖(terms.map fun t => radial t r * angular t m).sum -
        (terms.map fun t => radial t r * angular t n).sum‖ ≤ C * dist n m := by
  induction terms with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons t rest ih =>
    obtain ⟨C, hC, hc⟩ := ih
    obtain ⟨K, hK⟩ := ha t
    obtain ⟨R, hR⟩ := (hS.image (hr t)).isBounded.exists_norm_le
    refine ⟨max 0 R * (K : ℝ) + C, by positivity, fun r hrs n m => ?_⟩
    let f : A → ℂ := fun a => (rest.map fun t => radial t r * angular t a).sum
    change ‖radial t r * angular t m + f m - (radial t r * angular t n + f n)‖ ≤ _
    rw [show ∀ a b c d e : ℂ, a * b + c - (a * d + e) =
        a * (b - d) + (c - e) by intros; ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul, add_mul, mul_assoc]
    refine add_le_add ?_ (hc r hrs n m)
    have hl := hK.dist_le_mul m n
    rw [dist_eq_norm, dist_comm m n] at hl
    exact mul_le_mul ((hR _ ⟨r, hrs, rfl⟩).trans (le_max_right _ _))
      hl (norm_nonneg _) (le_max_left _ _)

end ConeCap
end Omega

