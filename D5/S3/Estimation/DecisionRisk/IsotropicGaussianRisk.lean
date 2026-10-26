/- GID: D5/S3/Estimation/DecisionRisk/IsotropicGaussianRisk
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/IsotropicGaussianRisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact equal-prior Gaussian risk over all measurable bounded randomized rules. -/

import D5.S3.Observer.Linear.GaussianObservationLaw
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Tactic.Module

/-! Equal-prior risk for actual affine Gaussian laws and bounded measurable rules. -/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.DecisionRisk.IsotropicGaussianRisk

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal InnerProductSpace RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

def law (μ : V) (σ : ℝ) : Measure V :=
  (stdGaussian V).map (fun z => μ + σ • z)

def risk (μ₀ μ₁ : V) (σ : ℝ) (q : V → ℝ) : ℝ :=
  ((∫ x, q x ∂law μ₀ σ) + (∫ x, 1 - q x ∂law μ₁ σ)) / 2

def phi (t : ℝ) : ℝ := (gaussianReal 0 1).real (Iic t)

def region (μ₀ μ₁ : V) : Set V :=
  {x | 0 ≤ ⟪μ₁ - μ₀, x - (1 / 2 : ℝ) • (μ₀ + μ₁)⟫_ℝ}

def midpoint (μ₀ μ₁ : V) : V → ℝ := (region μ₀ μ₁).indicator 1

private theorem law_probability (μ : V) (σ : ℝ) : IsProbabilityMeasure (law μ σ) := by
  unfold law
  infer_instance

private theorem region_measurable (μ₀ μ₁ : V) : MeasurableSet (region μ₀ μ₁) := by
  exact measurableSet_le measurable_const (by fun_prop)

private theorem midpoint_admissible (μ₀ μ₁ : V) :
    Measurable (midpoint μ₀ μ₁) ∧ ∀ x, 0 ≤ midpoint μ₀ μ₁ x ∧ midpoint μ₀ μ₁ x ≤ 1 := by
  refine ⟨measurable_const.indicator (region_measurable μ₀ μ₁), ?_⟩
  intro x
  by_cases hx : x ∈ region μ₀ μ₁ <;> simp [midpoint, hx]

/- This is an internal normalization of the existing D5 density supplier, not
   an additional public density API. The empty product is deliberately kept. -/
private theorem coordinate_common_density {n : Type} [Fintype n] [DecidableEq n]
    (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : EuclideanSpace ℝ n,
      law μ σ = (volume : Measure (EuclideanSpace ℝ n)).withDensity
        (fun x => ENNReal.ofReal (C * Real.exp (-‖x - μ‖ ^ 2 / (2 * σ ^ 2)))) := by
  classical
  let S : Matrix n n ℝ := σ ^ 2 • 1
  have hS : S.PosDef := Matrix.PosDef.one.smul (sq_pos_of_pos hσ)
  have hsquare : (σ • (1 : Matrix n n ℝ)) ^ 2 = S := by
    simp [S, pow_two, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hsqrt : CFC.sqrt S = σ • (1 : Matrix n n ℝ) := by
    rw [← hsquare, CFC.sqrt_sq _ (Matrix.PosSemidef.one.smul hσ.le).nonneg]
  have hinv : (σ • (1 : Matrix n n ℝ))⁻¹ = σ⁻¹ • (1 : Matrix n n ℝ) := by
    apply Matrix.inv_eq_left_inv
    simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hσ.ne']
  have hclm (a : ℝ) (x : EuclideanSpace ℝ n) :
      Matrix.toEuclideanCLM (𝕜 := ℝ) (a • (1 : Matrix n n ℝ)) x = a • x := by
    rw [map_smul, map_one]
    rfl
  have hlaw (μ : EuclideanSpace ℝ n) : law μ σ = multivariateGaussian μ S := by
    unfold law multivariateGaussian
    simp_rw [hsqrt, hclm]
  let K : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ Fintype.card n
  have hK : 0 < K := by dsimp [K]; positivity
  have hprod (x : EuclideanSpace ℝ n) :
      (∏ i, gaussianPDFReal 0 1 (x i)) = K * Real.exp (-‖x‖ ^ 2 / 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      ← Real.exp_sum, EuclideanSpace.real_norm_sq_eq]
    congr 1
    rw [← Finset.sum_div, ← Finset.sum_neg_distrib]
  obtain ⟨c, hc, hcfin, _, hcdet⟩ :=
    D5.S3.Observer.Linear.GaussianObservationLaw.multivariate_gaussian_density
      (0 : EuclideanSpace ℝ n) S hS
  refine ⟨c.toReal * K, mul_pos (ENNReal.toReal_pos hc.ne' hcfin) hK, ?_⟩
  intro μ
  obtain ⟨cμ, _, _, hdμ, hcμdet⟩ :=
    D5.S3.Observer.Linear.GaussianObservationLaw.multivariate_gaussian_density μ S hS
  have hcommon : cμ = c := hcμdet.trans hcdet.symm
  rw [hlaw, hdμ, hcommon, hsqrt, hinv]
  congr 1
  funext x
  rw [hclm, hprod, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hσ)]
  have hexp : -(σ⁻¹ * ‖x - μ‖) ^ 2 / 2 = -‖x - μ‖ ^ 2 / (2 * σ ^ 2) := by
    field_simp [hσ.ne']
    <;> ring
  rw [hexp]
  calc
    c * ENNReal.ofReal (K * Real.exp (-‖x - μ‖ ^ 2 / (2 * σ ^ 2))) =
        ENNReal.ofReal c.toReal *
          ENNReal.ofReal (K * Real.exp (-‖x - μ‖ ^ 2 / (2 * σ ^ 2))) := by
      rw [ENNReal.ofReal_toReal hcfin]
    _ = ENNReal.ofReal (c.toReal * (K * Real.exp (-‖x - μ‖ ^ 2 / (2 * σ ^ 2)))) :=
      (ENNReal.ofReal_mul ENNReal.toReal_nonneg).symm
    _ = _ := by congr 1; ring

private theorem common_density (σ : ℝ) (hσ : 0 < σ) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : V,
      law μ σ = (volume : Measure V).withDensity
        (fun x => ENNReal.ofReal (C * Real.exp (-‖x - μ‖ ^ 2 / (2 * σ ^ 2)))) := by
  classical
  let e : V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    (stdOrthonormalBasis ℝ V).repr
  obtain ⟨C, hC, hd⟩ := coordinate_common_density (n := Fin (Module.finrank ℝ V)) σ hσ
  refine ⟨C, hC, ?_⟩
  intro μ
  have hmap : (law μ σ).map e = law (e μ) σ := by
    change ((stdGaussian V).map (fun z => μ + σ • z)).map e =
      (stdGaussian (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))).map
        (fun z => e μ + σ • z)
    rw [← stdGaussian_map e, Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop)]
    congr 1
    funext z
    simp
  have hback : law μ σ = (law (e μ) σ).map e.symm := by
    rw [← hmap, Measure.map_map (by fun_prop) (by fun_prop)]
    simp (congrConsts := false) only [Function.comp_def, e.symm_apply_apply]
    exact Measure.map_id.symm
  rw [hback, hd]
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    withDensity_apply _ (hs.preimage (by fun_prop)), withDensity_apply _ hs]
  have hnorm (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :
      ‖e.symm x - μ‖ = ‖x - e μ‖ := by
    calc
      ‖e.symm x - μ‖ = ‖e (e.symm x - μ)‖ := (e.norm_map _).symm
      _ = ‖x - e μ‖ := by simp
  simp_rw [← hnorm]
  exact e.symm.measurePreserving.setLIntegral_comp_preimage_emb
    e.symm.toMeasurableEquiv.measurableEmbedding
    (fun x => ENNReal.ofReal (C * Real.exp (-‖x - μ‖ ^ 2 / (2 * σ ^ 2)))) s

private theorem bounded_integrable (P : Measure V) [IsFiniteMeasure P]
    (q : V → ℝ) (hq : Measurable q) (hb : ∀ x, 0 ≤ q x ∧ q x ≤ 1) : Integrable q P := by
  exact Integrable.of_mem_Icc 0 1 hq.aemeasurable (ae_of_all _ hb)

private theorem midpoint_norm_identity (μ₀ μ₁ x : V) :
    ‖x - μ₀‖ ^ 2 - ‖x - μ₁‖ ^ 2 =
      2 * ⟪μ₁ - μ₀, x - (1 / 2 : ℝ) • (μ₀ + μ₁)⟫_ℝ := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_smul_right, inner_add_right, real_inner_comm μ₁ μ₀,
    real_inner_comm μ₀ x, real_inner_comm μ₁ x]
  ring

private theorem all_rule_bound (μ₀ μ₁ : V) (σ : ℝ) (hσ : 0 < σ)
    (q : V → ℝ) (hq : Measurable q) (hb : ∀ x, 0 ≤ q x ∧ q x ≤ 1) :
    risk μ₀ μ₁ σ (midpoint μ₀ μ₁) ≤ risk μ₀ μ₁ σ q := by
  letI := law_probability μ₀ σ
  letI := law_probability μ₁ σ
  obtain ⟨C, hC, hd⟩ := common_density (V := V) σ hσ
  let f (μ : V) (x : V) : ℝ := C * Real.exp (-‖x - μ‖ ^ 2 / (2 * σ ^ 2))
  have hfm (μ : V) : Measurable (f μ) := by fun_prop
  have hf0 (μ : V) (x : V) : 0 ≤ f μ x := mul_nonneg hC.le (Real.exp_pos _).le
  have hLaw (μ : V) : law μ σ = volume.withDensity (fun x => ENNReal.ofReal (f μ x)) := hd μ
  have hfinite (μ : V) : ∀ᵐ x ∂(volume : Measure V), ENNReal.ofReal (f μ x) < ∞ :=
    ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have hreal (μ : V) (x : V) : (ENNReal.ofReal (f μ x)).toReal = f μ x :=
    ENNReal.toReal_ofReal (hf0 μ x)
  have hconvert (μ : V) (g : V → ℝ) :
      (∫ x, g x ∂law μ σ) = ∫ x, f μ x * g x ∂(volume : Measure V) := by
    rw [hLaw, integral_withDensity_eq_integral_toReal_smul (hfm μ).ennreal_ofReal (hfinite μ)]
    simp only [hreal, smul_eq_mul]
  have hint (μ : V) (g : V → ℝ) (hi : Integrable g (law μ σ)) :
      Integrable (fun x => f μ x * g x) (volume : Measure V) := by
    rw [hLaw] at hi
    have ht := (integrable_withDensity_iff_integrable_smul'
      (hfm μ).ennreal_ofReal (hfinite μ)).mp hi
    simpa only [hreal, smul_eq_mul] using ht
  obtain ⟨hqm, hqb⟩ := midpoint_admissible μ₀ μ₁
  have h1q : Measurable (fun x => 1 - q x) := measurable_const.sub hq
  have h1qb : ∀ x, 0 ≤ 1 - q x ∧ 1 - q x ≤ 1 := fun x => by
    obtain ⟨h0, h1⟩ := hb x
    constructor <;> linarith
  have h1m : Measurable (fun x => 1 - midpoint μ₀ μ₁ x) := measurable_const.sub hqm
  have h1mb : ∀ x, 0 ≤ 1 - midpoint μ₀ μ₁ x ∧ 1 - midpoint μ₀ μ₁ x ≤ 1 := fun x => by
    obtain ⟨h0, h1⟩ := hqb x
    constructor <;> linarith
  have hiq0 := hint μ₀ q (bounded_integrable _ q hq hb)
  have hiq1 := hint μ₁ (fun x => 1 - q x) (bounded_integrable _ _ h1q h1qb)
  have him0 := hint μ₀ (midpoint μ₀ μ₁) (bounded_integrable _ _ hqm hqb)
  have him1 := hint μ₁ (fun x => 1 - midpoint μ₀ μ₁ x)
    (bounded_integrable _ _ h1m h1mb)
  have hpoint (x : V) :
      f μ₀ x * midpoint μ₀ μ₁ x + f μ₁ x * (1 - midpoint μ₀ μ₁ x) ≤
        f μ₀ x * q x + f μ₁ x * (1 - q x) := by
    have hnorm := midpoint_norm_identity μ₀ μ₁ x
    have hden : 0 < 2 * σ ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hσ)
    by_cases hx : x ∈ region μ₀ μ₁
    · have hs : ‖x - μ₁‖ ^ 2 ≤ ‖x - μ₀‖ ^ 2 := by
        have hx' : 0 ≤ ⟪μ₁ - μ₀, x - (1 / 2 : ℝ) • (μ₀ + μ₁)⟫_ℝ := hx
        linarith
      have hf : f μ₀ x ≤ f μ₁ x := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hs) hden.le)) hC.le
      simp only [midpoint, Set.indicator_of_mem hx, Pi.one_apply, mul_one, sub_self, mul_zero,
        add_zero]
      nlinarith [mul_nonneg (h1qb x).1 (sub_nonneg.mpr hf)]
    · have hs : ‖x - μ₀‖ ^ 2 ≤ ‖x - μ₁‖ ^ 2 := by
        have hx' : ¬ 0 ≤ ⟪μ₁ - μ₀, x - (1 / 2 : ℝ) • (μ₀ + μ₁)⟫_ℝ := hx
        linarith
      have hf : f μ₁ x ≤ f μ₀ x := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg hs) hden.le)) hC.le
      simp only [midpoint, Set.indicator_of_notMem hx, mul_zero, sub_zero, mul_one, zero_add]
      nlinarith [mul_nonneg (hb x).1 (sub_nonneg.mpr hf)]
  have hcomp :
      (∫ x, f μ₀ x * midpoint μ₀ μ₁ x + f μ₁ x * (1 - midpoint μ₀ μ₁ x)
        ∂(volume : Measure V)) ≤
      (∫ x, f μ₀ x * q x + f μ₁ x * (1 - q x) ∂(volume : Measure V)) :=
    integral_mono (him0.add him1) (hiq0.add hiq1) hpoint
  rw [integral_add him0 him1, integral_add hiq0 hiq1] at hcomp
  unfold risk
  simp_rw (congrConsts := false) [hconvert]
  linarith

private theorem gaussian_right_tail (a : ℝ) :
    (gaussianReal 0 1).real (Ici a) = phi (-a) := by
  have hn : (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa only [neg_zero] using (gaussianReal_map_neg (μ := 0) (v := 1))
  unfold phi
  change ((gaussianReal 0 1) (Ici a)).toReal = ((gaussianReal 0 1) (Iic (-a))).toReal
  congr 1
  calc
    (gaussianReal 0 1) (Ici a) =
        ((gaussianReal 0 1).map (fun x : ℝ => -x)) (Iic (-a)) := by
      rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
      congr 1
      ext x
      simp only [Set.mem_Ici, Set.mem_preimage, Set.mem_Iic]
      constructor <;> intro h <;> linarith
    _ = _ := by rw [hn]

private theorem gaussian_left_tail (a : ℝ) :
    (gaussianReal 0 1).real (Iio a) = phi a := by
  letI : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  change ((gaussianReal 0 1) (Iio a)).toReal = ((gaussianReal 0 1) (Iic a)).toReal
  rw [measure_congr Iio_ae_eq_Iic]

private theorem phi_zero : phi 0 = 1 / 2 := by
  have hsum := probReal_add_probReal_compl (μ := gaussianReal 0 1)
    (s := Iio (0 : ℝ)) measurableSet_Iio
  rw [Set.compl_Iio, gaussian_left_tail, gaussian_right_tail, neg_zero] at hsum
  linarith

private theorem equal_means_risk (μ : V) (σ : ℝ) (q : V → ℝ)
    (hq : Measurable q) (hb : ∀ x, 0 ≤ q x ∧ q x ≤ 1) : risk μ μ σ q = 1 / 2 := by
  letI := law_probability μ σ
  have hi := bounded_integrable (law μ σ) q hq hb
  have hi' : Integrable (fun x => 1 - q x) (law μ σ) := (integrable_const 1).sub hi
  unfold risk
  rw [← integral_add hi hi']
  have hh : (fun x => q x + (1 - q x)) = (fun _ : V => (1 : ℝ)) := by
    funext x
    ring
  rw [hh]
  simp (congrConsts := false)

private theorem midpoint_risk (μ₀ μ₁ : V) (σ : ℝ) (hσ : 0 < σ) :
    risk μ₀ μ₁ σ (midpoint μ₀ μ₁) = phi (-‖μ₁ - μ₀‖ / (2 * σ)) := by
  classical
  by_cases hμ : μ₁ = μ₀
  · subst μ₁
    obtain ⟨hm, hb⟩ := midpoint_admissible μ₀ μ₀
    rw [equal_means_risk μ₀ σ _ hm hb]
    simp only [sub_self, norm_zero, neg_zero, zero_div, phi_zero]
  let δ : V := μ₁ - μ₀
  let r : ℝ := ‖δ‖
  have hr : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hμ)
  let e : V := r⁻¹ • δ
  have he : ‖e‖ = 1 := by
    dsimp only [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact inv_mul_cancel₀ hr.ne'
  let L : StrongDual ℝ V := innerSL ℝ e
  have hL (x : V) : L x = r⁻¹ * ⟪δ, x⟫_ℝ := by
    simp only [L, innerSL_apply_apply, e, real_inner_smul_left]
  have hproj : (stdGaussian V).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian]
    dsimp only [L]
    rw [innerSL_apply_norm, he]
    norm_num
  let a : ℝ := r / (2 * σ)
  let m : V := (1 / 2 : ℝ) • (μ₀ + μ₁)
  have hshift₀ (z : V) : μ₀ + σ • z - m = σ • z - (1 / 2 : ℝ) • δ := by
    dsimp only [m, δ]
    module
  have hshift₁ (z : V) : μ₁ + σ • z - m = σ • z + (1 / 2 : ℝ) • δ := by
    dsimp only [m, δ]
    module
  have hs₀ (z : V) : ⟪δ, μ₀ + σ • z - m⟫_ℝ = σ * r * (L z - a) := by
    rw [hshift₀, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hL]
    change σ * ⟪δ, z⟫_ℝ - (1 / 2 : ℝ) * r ^ 2 =
      σ * r * (r⁻¹ * ⟪δ, z⟫_ℝ - r / (2 * σ))
    field_simp [hσ.ne', hr.ne']
    <;> ring
  have hs₁ (z : V) : ⟪δ, μ₁ + σ • z - m⟫_ℝ = σ * r * (L z + a) := by
    rw [hshift₁, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hL]
    change σ * ⟪δ, z⟫_ℝ + (1 / 2 : ℝ) * r ^ 2 =
      σ * r * (r⁻¹ * ⟪δ, z⟫_ℝ + r / (2 * σ))
    field_simp [hσ.ne', hr.ne']
    <;> ring
  have hsr : 0 < σ * r := mul_pos hσ hr
  have hpre₀ : (fun z => μ₀ + σ • z) ⁻¹' region μ₀ μ₁ = L ⁻¹' Ici a := by
    ext z
    change (0 ≤ ⟪δ, μ₀ + σ • z - m⟫_ℝ) ↔ a ≤ L z
    rw [hs₀]
    calc
      (0 ≤ σ * r * (L z - a)) ↔ 0 ≤ L z - a :=
        mul_nonneg_iff_of_pos_left hsr
      _ ↔ a ≤ L z := sub_nonneg
  have hpre₁ : (fun z => μ₁ + σ • z) ⁻¹' (region μ₀ μ₁)ᶜ = L ⁻¹' Iio (-a) := by
    ext z
    change (¬ 0 ≤ ⟪δ, μ₁ + σ • z - m⟫_ℝ) ↔ L z < -a
    rw [hs₁]
    rw [mul_nonneg_iff_of_pos_left hsr]
    constructor <;> intro h <;> linarith
  have hA := region_measurable μ₀ μ₁
  have herr₀ : (law μ₀ σ).real (region μ₀ μ₁) = phi (-a) := by
    change ((law μ₀ σ) (region μ₀ μ₁)).toReal = _
    rw [law, Measure.map_apply (by fun_prop) hA, hpre₀,
      ← Measure.map_apply L.measurable measurableSet_Ici, hproj]
    exact gaussian_right_tail a
  have herr₁ : (law μ₁ σ).real (region μ₀ μ₁)ᶜ = phi (-a) := by
    change ((law μ₁ σ) (region μ₀ μ₁)ᶜ).toReal = _
    rw [law, Measure.map_apply (by fun_prop) hA.compl, hpre₁,
      ← Measure.map_apply L.measurable measurableSet_Iio, hproj]
    exact gaussian_left_tail (-a)
  have hi₀ : (∫ x, midpoint μ₀ μ₁ x ∂law μ₀ σ) = (law μ₀ σ).real (region μ₀ μ₁) :=
    integral_indicator_one hA
  have hsub : (fun x => 1 - midpoint μ₀ μ₁ x) = (region μ₀ μ₁)ᶜ.indicator 1 := by
    funext x
    by_cases hx : x ∈ region μ₀ μ₁ <;> simp [midpoint, hx]
  have hi₁ : (∫ x, 1 - midpoint μ₀ μ₁ x ∂law μ₁ σ) = (law μ₁ σ).real (region μ₀ μ₁)ᶜ := by
    rw [hsub, integral_indicator_one hA.compl]
  rw [risk, hi₀, hi₁, herr₀, herr₁]
  change (phi (-a) + phi (-a)) / 2 = phi (-r / (2 * σ))
  rw [show -a = -r / (2 * σ) by dsimp only [a]; ring]
  ring

/-- Exact equal-prior optimum over every measurable randomized binary rule.
    A rule returns the conditional probability of choosing label 1. -/
theorem isotropic_gaussian_optimal (μ₀ μ₁ : V) (σ : ℝ) (hσ : 0 < σ) :
    Measurable (midpoint μ₀ μ₁) ∧
    (∀ x, 0 ≤ midpoint μ₀ μ₁ x ∧ midpoint μ₀ μ₁ x ≤ 1) ∧
    risk μ₀ μ₁ σ (midpoint μ₀ μ₁) = phi (-‖μ₁ - μ₀‖ / (2 * σ)) ∧
    (∀ q : V → ℝ, Measurable q → (∀ x, 0 ≤ q x ∧ q x ≤ 1) →
      phi (-‖μ₁ - μ₀‖ / (2 * σ)) ≤ risk μ₀ μ₁ σ q) := by
  obtain ⟨hm, hb⟩ := midpoint_admissible μ₀ μ₁
  have heval := midpoint_risk μ₀ μ₁ σ hσ
  refine ⟨hm, hb, heval, ?_⟩
  intro q hq hqb
  rw [← heval]
  exact all_rule_bound μ₀ μ₁ σ hσ q hq hqb

end D5.S3.Estimation.DecisionRisk.IsotropicGaussianRisk



#check @D5.S3.Estimation.DecisionRisk.IsotropicGaussianRisk.isotropic_gaussian_optimal
#print axioms D5.S3.Estimation.DecisionRisk.IsotropicGaussianRisk.isotropic_gaussian_optimal
