/- GID: D5/S3/Analysis/RightHalfPlaneLogIntegral
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-profile-fourier4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The principal logarithm gives the ordinary cap integral in the right half-plane. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
Omega original.

The principal logarithm gives the ordinary cap integral in the right half-plane.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped Topology

namespace Omega

/-- The principal logarithm is a primitive of the reciprocal along a real
segment translated into the right half-plane. -/
theorem integral_inv_add_of_re_pos {d : ℂ} (hd : 0 < d.re) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in Ioo a b, ((t : ℂ) + d)⁻¹) =
      Complex.log ((b : ℂ) + d) - Complex.log ((a : ℂ) + d) := by
  have hslit {t : ℝ} (ht : t ∈ uIcc a b) : (t : ℂ) + d ∈ Complex.slitPlane := by
    rw [uIcc_of_le hab] at ht
    rw [Complex.mem_slitPlane_iff, Complex.add_re, Complex.ofReal_re]
    exact Or.inl (add_pos_of_nonneg_of_pos (ha.trans ht.1) hd)
  have hdiff (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) + d)) (((t : ℂ) + d)⁻¹) t := by
    have ht' : HasDerivAt (fun x : ℝ => (x : ℂ) + d) 1 t := by
      exact (Complex.ofRealCLM.hasFDerivAt.hasDerivAt).add_const d
    simpa [div_eq_mul_inv] using ht'.clog_real (hslit ht)
  have hi : IntervalIntegrable (fun t : ℝ => ((t : ℂ) + d)⁻¹) volume a b := by
    have hc : ContinuousOn (fun t : ℝ => ((t : ℂ) + d)⁻¹) (uIcc a b) := by
      apply (Complex.continuous_ofReal.add continuous_const).continuousOn.inv₀
      intro t ht
      exact Complex.slitPlane_ne_zero (hslit ht)
    exact hc.intervalIntegrable
  simpa only [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt hdiff hi

/-- The logarithm restricted to a nonzero imaginary argument records the oriented sign. -/
theorem log_I_mul_real {x : ℝ} (hx : x ≠ 0) :
    Complex.log (Complex.I * (x : ℂ)) =
      (Real.log |x| : ℂ) + ((Real.pi / 2 * (if 0 < x then 1 else -1) : ℝ) : ℂ) * Complex.I := by
  rcases lt_or_gt_of_ne hx with hn | hp
  · have h : Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * (-Complex.I) := by push_cast; ring
    rw [h, Complex.log_ofReal_mul (neg_pos.mpr hn) (neg_ne_zero.mpr Complex.I_ne_zero),
      Complex.log_neg_I, abs_of_neg hn, ite_eq_right hn.not_gt]
    push_cast
    ring
  · rw [mul_comm, Complex.log_ofReal_mul hp Complex.I_ne_zero, Complex.log_I,
      abs_of_pos hp, ite_eq_left hp]
    push_cast
    ring


/-- The principal logarithm is controlled by the logarithms of lower and
upper bounds for the modulus. -/
theorem norm_log_le_of_modulus_bounds {z : ℂ} {a b : ℝ}
    (ha : 0 < a) (hal : a ≤ ‖z‖) (hbu : ‖z‖ ≤ b) :
    ‖Complex.log z‖ ≤ |Real.log a| + |Real.log b| + Real.pi := by
  have hz := ha.trans_le hal
  have hlo := Real.log_le_log ha hal
  have hhi := Real.log_le_log hz hbu
  have hlog : |Real.log ‖z‖| ≤ |Real.log a| + |Real.log b| := by
    apply abs_le.mpr
    constructor
    · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
    · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]
  unfold Complex.log
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  linarith [Complex.abs_arg_le_pi z]

/-- A right regulator on imaginary arguments gives an ordinary weak limit
whenever the unregulated logarithm is absolutely integrable on the test support. -/
theorem tendsto_integral_log_real_add_I {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {x : X → ℝ} {f : X → ℂ}
    (hx : Measurable x) (hf : AEStronglyMeasurable f μ)
    {R B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ y ∂μ, |x y| ≤ R ∧ ‖f y‖ ≤ B)
    (hne : ∀ᵐ y ∂μ, x y ≠ 0)
    (hlog : Integrable (fun y => |Real.log (|x y|)|) μ) :
    Tendsto (fun ε : ℝ => ∫ y, f y * Complex.log ((ε : ℂ) + Complex.I * (x y : ℂ)) ∂μ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y, f y * Complex.log (Complex.I * (x y : ℂ)) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun y => B * ((|Real.log (1 + R)| + Real.pi) + |Real.log (|x y|)|))
  · exact .of_forall fun ε => hf.mul
      ((Complex.measurable_log.comp ((measurable_const.add (measurable_const.mul
        (Complex.continuous_ofReal.measurable.comp hx))))).aestronglyMeasurable)
  · have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo (0 : ℝ) 1 :=
      Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hε] with ε hε'
    filter_upwards [hbound, hne] with y hy hyne
    let z : ℂ := (ε : ℂ) + Complex.I * (x y : ℂ)
    have hlo : |x y| ≤ ‖z‖ := by
      have h := Complex.abs_im_le_norm z
      simpa [z, Complex.add_im, Complex.mul_im] using h
    have hhi : ‖z‖ ≤ 1 + R := calc
      _ ≤ ‖(ε : ℂ)‖ + ‖Complex.I * (x y : ℂ)‖ := norm_add_le _ _
      _ = ε + |x y| := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hε'.1]
      _ ≤ _ := add_le_add hε'.2.le hy.1
    change ‖f y * Complex.log z‖ ≤ _
    rw [norm_mul]
    have hlog' := norm_log_le_of_modulus_bounds (abs_pos.mpr hyne) hlo hhi
    exact mul_le_mul hy.2 (by linarith) (norm_nonneg _) hB
  · exact ((integrable_const (|Real.log (1 + R)| + Real.pi)).add hlog).const_mul B
  · filter_upwards [hne] with y hy
    have hslit : Complex.I * (x y : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      simpa [Complex.mul_im] using hy
    have hc : Continuous (fun ε : ℝ => (ε : ℂ) + Complex.I * (x y : ℂ)) :=
      Complex.continuous_ofReal.add continuous_const
    have ht : Tendsto (fun ε : ℝ => (ε : ℂ) + Complex.I * (x y : ℂ))
        (𝓝[>] 0) (𝓝 (Complex.I * (x y : ℂ))) := by
      simpa using
        (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    exact (ht.clog hslit).const_mul _


/-- The diagonal logarithm is integrable on the product of two bounded intervals. -/
theorem integrable_log_difference_unit :
    Integrable (fun p : ℝ × ℝ => |Real.log (|2 * (p.1 - p.2)|)|)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1))) := by
  let μ := volume.restrict (Ioo (0 : ℝ) 1)
  let f : ℝ → ℝ := fun t => |Real.log (|2 * t|)|
  let g : ℝ → ℝ := fun t => (Icc (-1 : ℝ) 1).indicator f t
  have hiL : IntervalIntegrable (fun t : ℝ => Real.log t) volume (-2) 2 :=
    intervalIntegral.intervalIntegrable_log'
  have hOn : IntegrableOn f (Icc (-1 : ℝ) 1) := by
    have h : IntervalIntegrable f volume (-1) 1 := by
      have h' : IntervalIntegrable (fun t : ℝ => |Real.log (2 * t)|) volume (-1) 1 := by
        convert hiL.abs.comp_mul_left (c := 2) using 1 <;> norm_num
      simpa only [f, Real.log_abs] using h'
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact h.1
  have hg : Integrable g := (integrable_indicator_iff measurableSet_Icc).mpr hOn
  have hgpos (t : ℝ) : 0 ≤ g t := Set.indicator_nonneg (fun t _ => abs_nonneg _) _
  let G : ℝ × ℝ → ℝ := fun p => g (p.1 - p.2)
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hms : Measurable g := hf.indicator measurableSet_Icc
  have hneg (t : ℝ) : g (-t) = g t := by
    have hh : -t ∈ Icc (-1 : ℝ) 1 ↔ t ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    by_cases ht : t ∈ Icc (-1 : ℝ) 1
    · simp [g, f, ht, hh.mpr ht, abs_mul]
    · simp [g, ht, mt hh.mp ht]
  have htranslate (u v : ℝ) : g (u - v) = g (v + -u) := by
    rw [← hneg (v + -u), show -(v + -u) = u - v by ring]
  have hm : AEStronglyMeasurable G (μ.prod μ) :=
    (hms.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  have hGint : Integrable G (μ.prod μ) := by
    apply (integrable_prod_iff hm).mpr
    have hs (u : ℝ) : Integrable (fun v => g (u - v)) :=
      ((measurePreserving_add_right (volume : Measure ℝ) (-u)).integrable_comp_of_integrable hg)
        |>.congr (.of_forall fun v => (htranslate u v).symm)
    refine ⟨.of_forall fun u => (hs u).integrableOn, ?_⟩
    apply (integrable_const (∫ t, g t)).mono' hm.norm.integral_prod_right'
    filter_upwards with u
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    calc
      _ ≤ ∫ v : ℝ, ‖G (u,v)‖ := setIntegral_le_integral (hs u).norm
        (.of_forall fun v => norm_nonneg _)
      _ = _ := by
        simp only [G, Real.norm_of_nonneg (hgpos _), htranslate]
        exact (measurePreserving_add_right (volume : Measure ℝ) (-u)).integral_comp
          (Homeomorph.addRight (-u)).toMeasurableEquiv.measurableEmbedding g
  have hloc : ∀ᵐ t ∂μ, t ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
  apply hGint.congr
  filter_upwards [(μ.quasiMeasurePreserving_fst (ν := μ)).ae hloc,
    (μ.quasiMeasurePreserving_snd (μ := μ)).ae hloc] with p hp hq
  have hm' : p.1 - p.2 ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hp.1, hp.2, hq.1, hq.2]
  simp [G, g, f, hm']


/-- A numerator vanishing with the square root of a nonnegative denominator
gives a dominated boundary limit as a right-half-plane shift tends to zero. -/
theorem tendsto_integral_div_add_of_sqrt_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {r : X → ℝ} {f : X → ℂ} {d : ℝ → X → ℂ}
    (hr : Measurable r) (hf : AEStronglyMeasurable f μ)
    (hd : ∀ ε, Measurable (d ε)) {B : ℝ} (hB : 0 ≤ B)
    (hpos : ∀ᵐ x ∂μ, 0 < r x)
    (hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ B * Real.sqrt (r x))
    (hi : Integrable (fun x => (Real.sqrt (r x))⁻¹) μ)
    (hRe : ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ᵐ x ∂μ, 0 ≤ (d ε x).re)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun ε => d ε x) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ∫ x, f x / ((r x : ℂ) + d ε x) ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, f x / (r x : ℂ) ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => B * (Real.sqrt (r x))⁻¹)
  · refine .of_forall fun ε => ?_
    have hm : Measurable (fun x => ((r x : ℂ) + d ε x)⁻¹) :=
      ((Complex.continuous_ofReal.measurable.comp hr).add (hd ε)).inv
    exact hf.mul hm.aestronglyMeasurable
  · filter_upwards [hRe] with ε hε
    filter_upwards [hpos, hb, hε] with x hx hxB hxε
    have hz : r x ≤ ‖(r x : ℂ) + d ε x‖ := by
      have hk := Complex.re_le_norm ((r x : ℂ) + d ε x)
      rw [Complex.add_re, Complex.ofReal_re] at hk
      linarith
    rw [norm_div]
    calc
      _ ≤ (B * Real.sqrt (r x)) / r x :=
        div_le_div_of_nonneg_left (norm_nonneg _) hx hz |>.trans
          (div_le_div_of_nonneg_right hxB hx.le)
      _ = _ := by
        have hroot := Real.sq_sqrt hx.le
        have hn := (Real.sqrt_pos.2 hx).ne'
        field_simp [hx.ne', hn]
        nlinarith
  · exact hi.const_mul B
  · filter_upwards [hpos, hlim] with x hx hxlim
    have hd' : Tendsto (fun ε => (r x : ℂ) + d ε x) (𝓝[>] 0) (𝓝 (r x : ℂ)) := by
      simpa using hxlim.const_add (r x : ℂ)
    exact tendsto_const_nhds.div hd' (Complex.ofReal_ne_zero.mpr hx.ne')


/-- The dimensionless radial regulator in the angular cap primitive. -/
def capShift (ε u v : ℝ) : ℂ :=
  (((ε ^ 2 : ℝ) : ℂ) + Complex.I * ((2 * ε * (u - v) : ℝ) : ℂ)) /
    ((2 * u * v : ℝ) : ℂ)

theorem capShift_re {ε u v : ℝ} :
    (capShift ε u v).re = ε ^ 2 / (2 * u * v) := by
  rw [capShift, Complex.div_ofReal_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

theorem continuous_capShift (u v : ℝ) : Continuous (fun ε => capShift ε u v) := by
  unfold capShift
  fun_prop

@[simp] theorem capShift_zero (u v : ℝ) : capShift 0 u v = 0 := by simp [capShift]

/-- The singular cap logarithm separates off the two radial normalization terms. -/
theorem log_capShift {ε u v : ℝ} (hε : 0 < ε) (hu : 0 < u) (hv : 0 < v) :
    Complex.log (capShift ε u v) =
      (Real.log ε - Real.log 2 - Real.log u - Real.log v : ℝ) +
      Complex.log ((ε : ℂ) + Complex.I * ((2 * (u - v) : ℝ) : ℂ)) := by
  let z : ℂ := (ε : ℂ) + Complex.I * ((2 * (u - v) : ℝ) : ℂ)
  have hz : z ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp [z, Complex.mul_re, hε.ne'] at h'
  have hd : 0 < 2 * u * v := by positivity
  have he : capShift ε u v = ((ε / (2 * u * v) : ℝ) : ℂ) * z := by
    unfold capShift z
    push_cast
    have huc : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
    have hvc : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
    field_simp [huc, hvc]
  rw [he, Complex.log_ofReal_mul (div_pos hε hd) hz, Real.log_div hε.ne' hd.ne',
    Real.log_mul (by positivity) hv.ne', Real.log_mul (by norm_num) hu.ne']
  dsimp [z]
  push_cast
  ring


/-- The cap integral under a constant-density projection to the interval from
minus one to one. -/
theorem mapped_cap_integral {X : Type*} [MeasurableSpace X] {σ : Measure X}
    {x : X → ℝ} (hx : Measurable x) {c : ℝ} (hc : 0 ≤ c)
    (hσ : Measure.map x σ = ENNReal.ofReal c • volume.restrict (Icc (-1 : ℝ) 1))
    {d : ℂ} (hd : 0 < d.re) :
    (∫ n, (1 - (x n : ℂ) + d)⁻¹ ∂σ) =
      (c : ℂ) * (Complex.log (2 + d) - Complex.log d) := by
  let f : ℝ → ℂ := fun t => (1 - (t : ℂ) + d)⁻¹
  have hf : Measurable f := by dsimp [f]; fun_prop
  change (∫ n, f (x n) ∂σ) = _
  rw [← integral_map hx.aemeasurable hf.aestronglyMeasurable, hσ,
    integral_smul_measure, ENNReal.toReal_ofReal hc]
  let g : ℝ → ℂ := fun t => ((t : ℂ) + d)⁻¹
  have h₁ : (∫ t in Icc (-1 : ℝ) 1, f t) = ∫ t in (-1 : ℝ)..1, f t := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
  have h₂ : (∫ t in (-1 : ℝ)..1, f t) = ∫ t in (0 : ℝ)..2, g t := by
    have h := intervalIntegral.integral_comp_sub_left (a := (-1 : ℝ)) (b := 1) g 1
    convert h using 1 <;> norm_num [g, f]
  have h₃ : (∫ t in (0 : ℝ)..2, g t) = Complex.log (2 + d) - Complex.log d := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Ioc_eq_integral_Ioo]
    simpa [g] using integral_inv_add_of_re_pos hd (a := 0) (b := 2)
      (by norm_num) (by norm_num)
  rw [h₁, h₂, h₃, Complex.real_smul]

/-- The square-root singularity in the angular denominator is integrable under
a constant-density cap projection. -/
theorem integrable_inv_sqrt_mapped_cap {X : Type*} [MeasurableSpace X] {σ : Measure X}
    {x : X → ℝ} (hx : Measurable x) {c : ℝ}
    (hσ : Measure.map x σ = ENNReal.ofReal c • volume.restrict (Icc (-1 : ℝ) 1)) :
    Integrable (fun n => (Real.sqrt (1 - x n))⁻¹) σ := by
  let g : ℝ → ℝ := fun t => (Real.sqrt t)⁻¹
  have hg : Measurable g := by dsimp [g]; fun_prop
  let f : ℝ → ℝ := fun t => g (1-t)
  have hf : Measurable f := hg.comp (measurable_const.sub measurable_id)
  apply (integrable_map_measure hf.aestronglyMeasurable hx.aemeasurable).mp
  rw [hσ]
  refine Integrable.smul_measure ?_ ENNReal.ofReal_ne_top
  have hi : IntervalIntegrable g volume 0 2 := by
    refine (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 2)
      (r := -(1 / 2 : ℝ)) (by norm_num)).congr ?_
    intro t ht
    have h : 0 ≤ t := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at ht
      exact ht.1.le
    change t ^ (-(1 / 2 : ℝ)) = (Real.sqrt t)⁻¹
    rw [Real.sqrt_eq_rpow, Real.rpow_neg h]
  have hsub : IntervalIntegrable f volume (-1) 1 := by
    have hh := hi.comp_sub_left (c := 1)
    norm_num at hh
    exact hh.symm
  change IntegrableOn f (Icc (-1 : ℝ) 1)
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact hsub.1


/-- The regular endpoint of the cap primitive converges in the integral with
a bounded coefficient supported at uniformly positive radii. -/
theorem tendsto_integral_log_two_add_capShift {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {u v : X → ℝ} {f : X → ℂ}
    (hu : Measurable u) (hv : Measurable v) (hf : AEStronglyMeasurable f μ)
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hb : ∀ᵐ y ∂μ, δ ≤ u y ∧ u y ≤ 1 ∧ δ ≤ v y ∧ v y ≤ 1 ∧ ‖f y‖ ≤ B) :
    Tendsto (fun ε : ℝ => ∫ y, f y * Complex.log (2 + capShift ε (u y) (v y)) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ y, f y * Complex.log 2 ∂μ)) := by
  let R := 2 + 3 / (2 * δ ^ 2)
  apply tendsto_integral_filter_of_dominated_convergence
    (fun _ : X => B * (|Real.log 2| + |Real.log R| + Real.pi))
  · refine .of_forall fun ε => hf.mul (show Measurable
      (fun y => Complex.log (2 + capShift ε (u y) (v y))) from ?_).aestronglyMeasurable
    unfold capShift
    fun_prop
  · have hε : ∀ᶠ ε : ℝ in 𝓝[>] 0, ε ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hε] with ε he
    filter_upwards [hb] with y hy
    obtain ⟨hdu, hu', hdv, hv', hbf⟩ := hy
    have hu₀ := hδ.trans_le hdu
    have hv₀ := hδ.trans_le hdv
    let z := 2 + capShift ε (u y) (v y)
    have hlow : 2 ≤ ‖z‖ := by
      have hr := Complex.re_le_norm z
      change (2 : ℝ) + (capShift ε (u y) (v y)).re ≤ _ at hr
      rw [capShift_re] at hr
      exact le_trans (le_add_of_nonneg_right (by positivity)) hr
    have hdist : |u y - v y| ≤ 1 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have he₀ : 0 ≤ 2 * ε := by linarith [he.1]
    have hnum : ‖(((ε ^ 2 : ℝ) : ℂ) + Complex.I *
        ((2 * ε * (u y - v y) : ℝ) : ℂ))‖ ≤ 3 := by
      apply (norm_add_le _ _).trans
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_mul, abs_of_pos (mul_pos (by norm_num) he.1)]
      have hsq := (sq_le_sq₀ he.1.le (by norm_num : (0 : ℝ) ≤ 1)).mpr he.2.le
      calc
        _ ≤ ε ^ 2 + 2 * ε * 1 := by gcongr
        _ ≤ _ := by nlinarith [he.2]
    have hden : 2 * δ ^ 2 ≤ 2 * u y * v y := by
      rw [pow_two, ← mul_assoc]
      gcongr
    have hupp : ‖z‖ ≤ R := by
      refine (norm_add_le _ _).trans ?_
      dsimp [R]
      rw [Complex.norm_ofNat, capShift, norm_div, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      gcongr
    rw [norm_mul]
    exact mul_le_mul hbf (norm_log_le_of_modulus_bounds (by norm_num) hlow hupp)
      (norm_nonneg _) hB
  · exact integrable_const _
  · refine .of_forall fun y => ?_
    have hs : Tendsto (fun ε => 2 + capShift ε (u y) (v y)) (𝓝[>] 0) (𝓝 (2 : ℂ)) := by
      have h := (continuous_capShift (u y) (v y)).continuousAt (x := (0 : ℝ))
      simpa using (h.tendsto.const_add (2 : ℂ)).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    exact (hs.clog (by simp)).const_mul _


/-- The weak limit of the cap logarithmic difference after the constant and
single-radius terms cancel in the testing coefficient. -/
theorem tendsto_integral_cap_logs {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {u v : X → ℝ} {f : X → ℂ}
    (hu : Measurable u) (hv : Measurable v) (hf : AEStronglyMeasurable f μ)
    {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hb : ∀ᵐ y ∂μ, δ ≤ u y ∧ u y ≤ 1 ∧ δ ≤ v y ∧ v y ≤ 1 ∧ ‖f y‖ ≤ B)
    (hne : ∀ᵐ y ∂μ, u y ≠ v y)
    (hlog : Integrable (fun y => |Real.log (|2 * (u y - v y)|)|) μ)
    (hf0 : (∫ y, f y ∂μ) = 0)
    (hfu : (∫ y, f y * (Real.log (u y) : ℂ) ∂μ) = 0)
    (hfv : (∫ y, f y * (Real.log (v y) : ℂ) ∂μ) = 0) :
    Tendsto (fun ε : ℝ => ∫ y, f y *
      (Complex.log (2 + capShift ε (u y) (v y)) - Complex.log (capShift ε (u y) (v y))) ∂μ)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(∫ y, f y * Complex.log (Complex.I * ((2 * (u y - v y) : ℝ) : ℂ)) ∂μ))) := by
  let x : X → ℝ := fun y => 2 * (u y - v y)
  have hx : Measurable x := measurable_const.mul (hu.sub hv)
  have hxB : ∀ᵐ y ∂μ, |x y| ≤ 2 ∧ ‖f y‖ ≤ B := by
    filter_upwards [hb] with y hy
    refine ⟨?_, hy.2.2.2.2⟩
    dsimp [x]
    have h : |u y - v y| ≤ 1 := abs_le.mpr
      ⟨by linarith [hy.1, hy.2.2.2.1], by linarith [hy.2.1, hy.2.2.1]⟩
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hxn := hne.mono fun y hy => mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (sub_ne_zero.mpr hy)
  have hs := tendsto_integral_log_real_add_I hx hf hB hxB hxn hlog
  have ht := tendsto_integral_log_two_add_capShift hu hv hf hδ hB hb
  rw [integral_mul_const, hf0, zero_mul] at ht
  have hlim := ht.sub hs
  simp only [zero_sub] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  let A : X → ℂ := fun y => Complex.log (2 + capShift ε (u y) (v y))
  let C : X → ℂ := fun y => Complex.log ((ε : ℂ) + Complex.I * (x y : ℂ))
  let U : X → ℂ := fun y => Real.log (u y)
  let V : X → ℂ := fun y => Real.log (v y)
  let a : ℂ := (Real.log ε - Real.log 2 : ℝ)
  have hfm : Integrable f μ := (integrable_const B).mono' hf (hb.mono fun _ hy => hy.2.2.2.2)
  have hU₀ (w : X → ℝ) (hw : Measurable w) (hw' : ∀ᵐ y ∂μ, δ ≤ w y ∧ w y ≤ 1) :
      Integrable (fun y => f y * (Real.log (w y) : ℂ)) μ := by
    apply (integrable_const (B * |Real.log δ|)).mono' (hf.mul
      ((Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp hw)).aestronglyMeasurable))
    filter_upwards [hw', hxB] with y hy hf'
    change ‖f y * (Real.log (w y) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul hf'.2 _ (abs_nonneg _) hB
    have hl := Real.log_le_log hδ hy.1
    have hu₁ := Real.log_nonpos (hδ.trans_le hy.1).le hy.2
    have hδ' := Real.log_nonpos hδ.le (hy.1.trans hy.2)
    simpa only [abs_of_nonpos hu₁, abs_of_nonpos hδ', neg_le_neg_iff] using hl
  have hU : Integrable (fun y => f y * U y) μ := hU₀ u hu (hb.mono fun _ hy => ⟨hy.1, hy.2.1⟩)
  have hV : Integrable (fun y => f y * V y) μ :=
    hU₀ v hv (hb.mono fun _ hy => ⟨hy.2.2.1, hy.2.2.2.1⟩)
  have hC : Integrable (fun y => f y * C y) μ := by
    have hm : Measurable C := by unfold C; fun_prop
    apply (integrable_const (B * (|Real.log ε| + |Real.log (ε + 2)| + Real.pi))).mono'
      (hf.mul hm.aestronglyMeasurable)
    filter_upwards [hxB] with y hy
    let z := (ε : ℂ) + Complex.I * (x y : ℂ)
    have hl : ε ≤ ‖z‖ := by simpa [z, Complex.mul_re] using Complex.re_le_norm z
    have hu' : ‖z‖ ≤ ε + 2 := by
      refine (norm_add_le _ _).trans ?_
      simp [Complex.norm_real, abs_of_pos hε, hy.1]
    change ‖f y * C y‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hy.2 (norm_log_le_of_modulus_bounds hε hl hu') (norm_nonneg _) hB
  have hA : Integrable (fun y => f y * A y) μ := by
    have hm : Measurable A := by unfold A capShift; fun_prop
    let R := 2 + (ε ^ 2 + 2 * ε) / (2 * δ ^ 2)
    apply (integrable_const (B * (|Real.log 2| + |Real.log R| + Real.pi))).mono'
      (hf.mul hm.aestronglyMeasurable)
    filter_upwards [hb] with y hy
    obtain ⟨hdu, hu', hdv, hv', hbf⟩ := hy
    have hu₀ := hδ.trans_le hdu
    have hv₀ := hδ.trans_le hdv
    let z := (2 : ℂ) + capShift ε (u y) (v y)
    have hlow : (2 : ℝ) ≤ ‖z‖ := by
      have hr := Complex.re_le_norm z
      change (2 : ℝ) + (capShift ε (u y) (v y)).re ≤ _ at hr
      rw [capShift_re] at hr
      exact le_trans (le_add_of_nonneg_right (by positivity)) hr
    have hd : |u y - v y| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hn : ‖(((ε ^ 2 : ℝ) : ℂ) + Complex.I * ((2 * ε * (u y - v y) : ℝ) : ℂ))‖ ≤
        ε ^ 2 + 2 * ε := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
        abs_mul, abs_of_pos (mul_pos (by norm_num) hε)]
      nlinarith [mul_le_mul_of_nonneg_left hd (show 0 ≤ 2 * ε by positivity)]
    have hden : 2 * δ ^ 2 ≤ 2 * u y * v y := by
      rw [pow_two, ← mul_assoc]
      gcongr
    have hupp : ‖z‖ ≤ R := by
      apply (norm_add_le _ _).trans
      dsimp [R]
      rw [Complex.norm_ofNat, capShift, norm_div, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      gcongr
    change ‖f y * A y‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul hbf (norm_log_le_of_modulus_bounds (by norm_num) hlow hupp)
      (norm_nonneg _) hB
  change (∫ y, f y * A y ∂μ) - (∫ y, f y * C y ∂μ) = _
  have heq : (fun y => f y * (A y - Complex.log (capShift ε (u y) (v y)))) =ᵐ[μ]
      fun y => f y * A y - (f y * a - f y * U y - f y * V y + f y * C y) := by
    filter_upwards [hb] with y hy
    rw [log_capShift hε (hδ.trans_le hy.1) (hδ.trans_le hy.2.2.1)]
    dsimp [a, U, V, C, x]
    push_cast
    ring
  rw [integral_congr_ae heq]
  let D := (((fun y => f y * a) - fun y => f y * U y) - fun y => f y * V y) +
    fun y => f y * C y
  change _ = ∫ y, f y * A y - D y ∂μ
  have hD : Integrable D μ := (((hfm.mul_const a).sub hU).sub hV).add hC
  rw [integral_sub hA hD]
  unfold D
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [integral_add (f := fun y => f y * a - f y * U y - f y * V y)
    (((hfm.mul_const a).sub hU).sub hV) hC]
  rw [integral_sub (f := fun y => f y * a - f y * U y) ((hfm.mul_const a).sub hU) hV,
    integral_sub (hfm.mul_const a) hU, integral_mul_const, hf0]
  have hu₀ : (∫ y, f y * U y ∂μ) = 0 := hfu
  have hv₀ : (∫ y, f y * V y ∂μ) = 0 := hfv
  rw [hu₀, hv₀]
  ring

end Omega

