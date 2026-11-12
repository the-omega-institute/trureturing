/- GID: D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Extended convex endpoint limits from positive Stieltjes curvature. -/
import D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic

/-! Endpoint values are a finite affine term plus nonnegative extended curvature mass.
This convention never subtracts infinite values. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Analytic.Convexity.CurvatureHingeRepresentation

open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {f : ℝ → ℝ}

private def one : Positive := ⟨1, by norm_num⟩

private def lowerMass (hf : ConvexOn ℝ (Ioi 0) f) (s : Positive) : ℝ≥0∞ :=
  ∫⁻ t in Iic one, ENNReal.ofReal ((t : ℝ) - s) ∂curvature hf

private def upperMassRatio (hf : ConvexOn ℝ (Ioi 0) f) (s : Positive) : ℝ≥0∞ :=
  ∫⁻ t in Ioi one, ENNReal.ofReal (1 - (t : ℝ) / s) ∂curvature hf

/-- The value at zero, allowing positive infinity. -/
def zeroEndpoint (hf : ConvexOn ℝ (Ioi 0) f) : EReal :=
  ((f 1 - rightDeriv f 1 : ℝ) : EReal) +
    (∫⁻ t in Iic one, ENNReal.ofReal (t : ℝ) ∂curvature hf : ℝ≥0∞)

/-- The asymptotic slope, allowing positive infinity and infinite total tail curvature. -/
def infinityEndpoint (hf : ConvexOn ℝ (Ioi 0) f) : EReal :=
  (rightDeriv f 1 : EReal) + (curvature hf (Ioi one) : ℝ≥0∞)

private lemma lowerMass_antitone (hf : ConvexOn ℝ (Ioi 0) f) : Antitone (lowerMass hf) := by
  intro s u hsu
  apply lintegral_mono
  intro t
  exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (show (s : ℝ) ≤ u from hsu) (t : ℝ))

private lemma upperMassRatio_monotone (hf : ConvexOn ℝ (Ioi 0) f) :
    Monotone (upperMassRatio hf) := by
  intro s u hsu
  apply lintegral_mono
  intro t
  apply ENNReal.ofReal_le_ofReal
  exact sub_le_sub_left (div_le_div_of_nonneg_left (show (0 : ℝ) ≤ t from t.property.le)
    (show (0 : ℝ) < s from s.property) (show (s : ℝ) ≤ u from hsu)) 1

private def small (n : ℕ) : Positive := ⟨1 / ((n : ℝ) + 1), by change (0 : ℝ) < _; positivity⟩

private lemma small_antitone : Antitone small := by
  intro m n hmn
  change 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1)
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

private lemma small_tendsto_zero : Tendsto (fun n => (small n : ℝ)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private lemma small_tendsto_atBot : Tendsto small atTop atBot := by
  apply tendsto_atBot.2
  intro a
  exact (small_tendsto_zero.eventually (gt_mem_nhds a.property)).mono fun _ hn => hn.le

private lemma positive_val_tendsto_zero :
    Tendsto (fun s : Positive => (s : ℝ)) atBot (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall fun s => ha.trans s.property
  · intro a ha
    have he := eventually_le_atBot (⟨a / 2, by change (0 : ℝ) < _; positivity⟩ : Positive)
    exact he.mono fun s hs => (show (s : ℝ) ≤ a / 2 from hs).trans_lt (by linarith)

private lemma lowerMass_tendsto (hf : ConvexOn ℝ (Ioi 0) f) :
    Tendsto (lowerMass hf) atBot
      (𝓝 (∫⁻ t in Iic one, ENNReal.ofReal (t : ℝ) ∂curvature hf)) := by
  have hs : Tendsto (fun n => lowerMass hf (small n)) atTop
      (𝓝 (∫⁻ t in Iic one, ENNReal.ofReal (t : ℝ) ∂curvature hf)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact (measurable_subtype_coe.sub_const _).ennreal_ofReal.aemeasurable
    · exact Eventually.of_forall fun t m n hmn =>
        ENNReal.ofReal_le_ofReal (sub_le_sub_left (show (small n : ℝ) ≤ small m from small_antitone hmn) (t : ℝ))
    · apply Eventually.of_forall
      intro t
      simpa only [sub_zero, Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_const_nhds.sub small_tendsto_zero :
            Tendsto (fun n => (t : ℝ) - small n) atTop (𝓝 ((t : ℝ) - 0)))
  have hi := tendsto_atBot_iSup (lowerMass_antitone hf)
  have he := tendsto_nhds_unique (hi.comp small_tendsto_atBot) hs
  simpa only [he] using hi

private def large (n : ℕ) : Positive := ⟨(n : ℝ) + 1, by change (0 : ℝ) < _; positivity⟩

private lemma large_monotone : Monotone large := by
  intro m n hmn
  change (m : ℝ) + 1 ≤ (n : ℝ) + 1
  exact_mod_cast Nat.add_le_add_right hmn 1

private lemma large_tendsto_atTop : Tendsto large atTop atTop := by
  apply tendsto_atTop.2
  intro a
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact (tendsto_atTop.1 ht (a : ℝ)).mono fun _ hn => hn

private lemma positive_val_tendsto_atTop :
    Tendsto (fun s : Positive => (s : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro a
  exact (eventually_ge_atTop (⟨max a 1, by change (0 : ℝ) < _; positivity⟩ : Positive)).mono
    fun s hs => (le_max_left a 1).trans hs

private lemma upperMassRatio_tendsto (hf : ConvexOn ℝ (Ioi 0) f) :
    Tendsto (upperMassRatio hf) atTop (𝓝 (curvature hf (Ioi one))) := by
  have hs : Tendsto (fun n => upperMassRatio hf (large n)) atTop
      (𝓝 (∫⁻ _t in Ioi one, (1 : ℝ≥0∞) ∂curvature hf)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
    · intro n
      exact (measurable_const.sub (measurable_subtype_coe.div_const _)).ennreal_ofReal.aemeasurable
    · exact Eventually.of_forall fun t m n hmn =>
        ENNReal.ofReal_le_ofReal (sub_le_sub_left
          (div_le_div_of_nonneg_left (show (0 : ℝ) ≤ t from t.property.le)
            (show (0 : ℝ) < large m from (large m).property)
            (show (large m : ℝ) ≤ large n from large_monotone hmn)) (1 : ℝ))
    · apply Eventually.of_forall
      intro t
      have ht : Tendsto (fun n => (t : ℝ) / (large n : ℝ)) atTop (𝓝 0) :=
        by
        simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
          (tendsto_const_nhds (x := (t : ℝ))).mul (tendsto_inv_atTop_zero.comp
            (positive_val_tendsto_atTop.comp large_tendsto_atTop))
      simpa only [sub_zero, ENNReal.ofReal_one, Function.comp_def] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (tendsto_const_nhds.sub ht :
            Tendsto (fun n => 1 - (t : ℝ) / (large n : ℝ)) atTop (𝓝 (1 - 0)))
  simp only [lintegral_const, Measure.restrict_apply_univ, one_mul] at hs
  have hi := tendsto_atTop_iSup (upperMassRatio_monotone hf)
  have he := tendsto_nhds_unique (hi.comp large_tendsto_atTop) hs
  simpa only [he] using hi

private lemma coe_lowerMass (hf : ConvexOn ℝ (Ioi 0) f) (s : Positive) :
    (lowerMass hf s : EReal) =
      ((∫ t in Iic one, max ((t : ℝ) - s) 0 ∂curvature hf : ℝ) : EReal) := by
  have hi := negative_hinge_integrable hf one s
  have hn : 0 ≤ᵐ[(curvature hf).restrict (Iic one)]
      (fun t : Positive => max ((t : ℝ) - s) 0) :=
    Eventually.of_forall fun t => le_max_right _ _
  have he := ofReal_integral_eq_lintegral_ofReal hi hn
  have hm : lowerMass hf s = ENNReal.ofReal
      (∫ t in Iic one, max ((t : ℝ) - s) 0 ∂curvature hf) := by
    rw [he]
    simp [lowerMass]
  rw [hm, EReal.coe_ennreal_ofReal, max_eq_left]
  exact_mod_cast integral_nonneg_of_ae hn

private lemma coe_lower_representation (hf : ConvexOn ℝ (Ioi 0) f)
    {s : Positive} (hs : s ≤ one) :
    (f s : EReal) = ((f 1 + rightDeriv f 1 * ((s : ℝ) - 1) : ℝ) : EReal) + lowerMass hf s := by
  have he := scalar_hinge_representation hf one s
  have hz : (∫ t in Ioi one, max ((s : ℝ) - t) 0 ∂curvature hf) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    exact max_eq_right (sub_nonpos.mpr ((show s ≤ one from hs).trans ht.le))
  rw [hz, add_zero] at he
  rw [coe_lowerMass, ← EReal.coe_add]
  exact congrArg (fun x : ℝ => (x : EReal)) he

/-- Every real convex function on the positive ray has a zero endpoint in
`Real union {+infinity}`, with the explicit curvature value. -/
theorem tendsto_zeroEndpoint (hf : ConvexOn ℝ (Ioi 0) f) :
    Tendsto (fun s : Positive => (f s : EReal)) atBot (𝓝 (zeroEndpoint hf)) := by
  have ha : Tendsto (fun s : Positive =>
      ((f 1 + rightDeriv f 1 * ((s : ℝ) - 1) : ℝ) : EReal)) atBot
      (𝓝 ((f 1 - rightDeriv f 1 : ℝ) : EReal)) := by
    apply continuous_coe_real_ereal.continuousAt.tendsto.comp
    convert tendsto_const_nhds.add
      (tendsto_const_nhds.mul (positive_val_tendsto_zero.sub tendsto_const_nhds)) using 1 <;> simp [one] <;> ring
  have hl := continuous_coe_ennreal_ereal.continuousAt.tendsto.comp (lowerMass_tendsto hf)
  have hh := (EReal.continuousAt_add
    (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))).tendsto.comp (ha.prodMk_nhds hl)
  apply hh.congr'
  filter_upwards [eventually_le_atBot one] with s hs
  exact (coe_lower_representation hf hs).symm

private lemma coe_upperMassRatio (hf : ConvexOn ℝ (Ioi 0) f) (s : Positive) :
    (upperMassRatio hf s : EReal) =
      ((∫ t in Ioi one, max (1 - (t : ℝ) / s) 0 ∂curvature hf : ℝ) : EReal) := by
  have heq : (fun t : Positive => max (1 - (t : ℝ) / s) 0) =
      fun t : Positive => ((s : ℝ))⁻¹ * max ((s : ℝ) - t) 0 := by
    funext t
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr s.property.le), mul_zero]
    congr 1
    field_simp [(show (0 : ℝ) < s from s.property).ne'] <;> ring
  have hi : IntegrableOn (fun t : Positive => max (1 - (t : ℝ) / s) 0)
      (Ioi one) (curvature hf) := by
    rw [heq]
    exact (positive_hinge_integrable hf one s).const_mul _
  have hn : 0 ≤ᵐ[(curvature hf).restrict (Ioi one)]
      (fun t : Positive => max (1 - (t : ℝ) / s) 0) :=
    Eventually.of_forall fun t => le_max_right _ _
  have he := ofReal_integral_eq_lintegral_ofReal hi hn
  have hm : upperMassRatio hf s = ENNReal.ofReal
      (∫ t in Ioi one, max (1 - (t : ℝ) / s) 0 ∂curvature hf) := by
    rw [he]
    simp [upperMassRatio]
  rw [hm, EReal.coe_ennreal_ofReal, max_eq_left]
  exact_mod_cast integral_nonneg_of_ae hn

private lemma coe_upper_representation (hf : ConvexOn ℝ (Ioi 0) f)
    {s : Positive} (hs : one ≤ s) :
    ((f s / (s : ℝ) : ℝ) : EReal) =
      ((f 1 / (s : ℝ) + rightDeriv f 1 * (1 - 1 / (s : ℝ)) : ℝ) : EReal) + upperMassRatio hf s := by
  have he := scalar_hinge_representation hf one s
  have hz : (∫ t in Iic one, max ((t : ℝ) - s) 0 ∂curvature hf) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    exact max_eq_right (sub_nonpos.mpr (show (t : ℝ) ≤ s from ht.trans hs))
  rw [hz, add_zero] at he
  rw [coe_upperMassRatio, ← EReal.coe_add]
  apply congrArg (fun x : ℝ => (x : EReal))
  have heq : (fun t : Positive => max (1 - (t : ℝ) / s) 0) =
      fun t : Positive => ((s : ℝ))⁻¹ * max ((s : ℝ) - t) 0 := by
    funext t
    rw [mul_max_of_nonneg _ _ (inv_nonneg.mpr s.property.le), mul_zero]
    congr 1
    field_simp [(show (0 : ℝ) < s from s.property).ne'] <;> ring
  rw [heq, integral_const_mul, he]
  change (f 1 + rightDeriv f 1 * ((s : ℝ) - 1) + _) / (s : ℝ) = _
  field_simp [(show (0 : ℝ) < s from s.property).ne'] <;> ring

/-- The asymptotic slope exists and equals the finite affine slope plus the possibly
infinite curvature mass on `(1,infinity)`. -/
theorem tendsto_infinityEndpoint (hf : ConvexOn ℝ (Ioi 0) f) :
    Tendsto (fun s : Positive => ((f s / (s : ℝ) : ℝ) : EReal)) atTop
      (𝓝 (infinityEndpoint hf)) := by
  have hinv : Tendsto (fun s : Positive => ((s : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp positive_val_tendsto_atTop
  have ha : Tendsto (fun s : Positive =>
      ((f 1 / (s : ℝ) + rightDeriv f 1 * (1 - 1 / (s : ℝ)) : ℝ) : EReal)) atTop
      (𝓝 (rightDeriv f 1 : EReal)) := by
    apply continuous_coe_real_ereal.continuousAt.tendsto.comp
    simp only [div_eq_mul_inv, one_mul]
    convert (tendsto_const_nhds.mul hinv).add
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub hinv)) using 1 <;> simp [one] <;> ring
  have hl := continuous_coe_ennreal_ereal.continuousAt.tendsto.comp (upperMassRatio_tendsto hf)
  have hh := (EReal.continuousAt_add
    (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))).tendsto.comp (ha.prodMk_nhds hl)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop one] with s hs
  exact (coe_upper_representation hf hs).symm

/-- The nonnegative part of the closed perspective after subtracting its affine support.
Both integrals are extended nonnegative integrals, including on the axes. -/
def curvatureRemainder (hf : ConvexOn ℝ (Ioi 0) f) (u v : ℝ) : ℝ≥0∞ :=
  (∫⁻ t in Iic one, ENNReal.ofReal ((t : ℝ) * v - u) ∂curvature hf) +
    ∫⁻ t in Ioi one, ENNReal.ofReal (u - (t : ℝ) * v) ∂curvature hf

/-- The perspective with the actual convex endpoint limits. Multiplication by zero
at the origin gives zero even when an endpoint is infinite. -/
def closedPerspective (hf : ConvexOn ℝ (Ioi 0) f) (u v : ℝ) : EReal :=
  if v = 0 then (u : EReal) * infinityEndpoint hf
  else if u = 0 then (v : EReal) * zeroEndpoint hf
  else ((v * f (u / v) : ℝ) : EReal)

private lemma coe_lintegral_max {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hi : Integrable (fun x => max (g x) 0) μ) :
    ((∫⁻ x, ENNReal.ofReal (g x) ∂μ : ℝ≥0∞) : EReal) =
      ((∫ x, max (g x) 0 ∂μ : ℝ) : EReal) := by
  have hn : 0 ≤ᵐ[μ] (fun x => max (g x) 0) :=
    Eventually.of_forall fun x => le_max_right _ _
  have he := ofReal_integral_eq_lintegral_ofReal hi hn
  have hm : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) =
      ENNReal.ofReal (∫ x, max (g x) 0 ∂μ) := by
    rw [he]
    simp
  rw [hm, EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg_of_ae hn)]

private lemma curvatureRemainder_positive (hf : ConvexOn ℝ (Ioi 0) f)
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (curvatureRemainder hf u v : EReal) =
      ((∫ t in Iic one, max ((t : ℝ) * v - u) 0 ∂curvature hf : ℝ) : EReal) +
      ((∫ t in Ioi one, max (u - (t : ℝ) * v) 0 ∂curvature hf : ℝ) : EReal) := by
  have hn : (fun t : Positive => max ((t : ℝ) * v - u) 0) =
      fun t : Positive => v * max ((t : ℝ) - u / v) 0 := by
    funext t
    rw [mul_max_of_nonneg _ _ hv.le, mul_zero]
    congr 1
    field_simp
    <;> ring
  have hp : (fun t : Positive => max (u - (t : ℝ) * v) 0) =
      fun t : Positive => v * max (u / v - (t : ℝ)) 0 := by
    funext t
    rw [mul_max_of_nonneg _ _ hv.le, mul_zero]
    congr 1
    field_simp
    <;> ring
  have hin : IntegrableOn (fun t : Positive => max ((t : ℝ) * v - u) 0)
      (Iic one) (curvature hf) := by
    rw [hn]
    exact (negative_hinge_integrable hf one ⟨u / v, div_pos hu hv⟩).const_mul v
  have hip : IntegrableOn (fun t : Positive => max (u - (t : ℝ) * v) 0)
      (Ioi one) (curvature hf) := by
    rw [hp]
    exact (positive_hinge_integrable hf one ⟨u / v, div_pos hu hv⟩).const_mul v
  rw [curvatureRemainder, EReal.coe_ennreal_add, coe_lintegral_max hin, coe_lintegral_max hip]

/-- The scalar hinge representation holds on the entire closed nonnegative quadrant,
with the proved endpoint limits, infinite curvature allowed, and no infinite subtraction. -/
theorem closedPerspective_eq_affine_add_curvature (hf : ConvexOn ℝ (Ioi 0) f)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    closedPerspective hf u v =
      ((f 1 * v + rightDeriv f 1 * (u - v) : ℝ) : EReal) +
        (curvatureRemainder hf u v : EReal) := by
  by_cases hv0 : v = 0
  · subst v
    have hn : (∫⁻ t in Iic one, ENNReal.ofReal ((t : ℝ) * 0 - u) ∂curvature hf) = 0 := by
      simp [ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hu)]
    have hp : (∫⁻ t in Ioi one, ENNReal.ofReal (u - (t : ℝ) * 0) ∂curvature hf) =
        ENNReal.ofReal u * curvature hf (Ioi one) := by simp
    rw [curvatureRemainder, hn, hp, zero_add]
    simp only [closedPerspective, ↓reduceIte, infinityEndpoint, mul_zero, zero_add, sub_zero]
    rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hu) (EReal.coe_ne_top _),
      ← EReal.coe_mul, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hu]
    congr 1
    congr 1
    ring
  · by_cases hu0 : u = 0
    · subst u
      have hn : (∫⁻ t in Iic one, ENNReal.ofReal ((t : ℝ) * v - 0) ∂curvature hf) =
          ENNReal.ofReal v * ∫⁻ t in Iic one, ENNReal.ofReal (t : ℝ) ∂curvature hf := by
        simp only [sub_zero, mul_comm (a := (_ : ℝ)) v, ENNReal.ofReal_mul hv]
        exact lintegral_const_mul _ measurable_subtype_coe.ennreal_ofReal
      have hp : (∫⁻ t in Ioi one, ENNReal.ofReal (0 - (t : ℝ) * v) ∂curvature hf) = 0 := by
        apply (lintegral_eq_zero_iff
          (measurable_const.sub (measurable_subtype_coe.mul_const v)).ennreal_ofReal).2
        exact Eventually.of_forall fun t =>
          ENNReal.ofReal_eq_zero.mpr (by
            change 0 - (t : ℝ) * v ≤ 0
            exact sub_nonpos.mpr (mul_nonneg t.property.le hv))
      rw [curvatureRemainder, hn, hp, add_zero]
      simp only [closedPerspective, hv0, ↓reduceIte, zeroEndpoint]
      rw [EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hv) (EReal.coe_ne_top _),
        ← EReal.coe_mul, EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hv]
      congr 1
      congr 1
      ring
    · have hu' : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hv' : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
      rw [closedPerspective, if_neg hv0, if_neg hu0, curvatureRemainder_positive hf hu' hv',
        ← EReal.coe_add, ← EReal.coe_add]
      apply congrArg (fun x : ℝ => (x : EReal))
      simpa only [one, add_assoc] using perspective_positive hf hu' hv'

/-- In particular the closed perspective assigns zero to the origin. -/
theorem closedPerspective_origin (hf : ConvexOn ℝ (Ioi 0) f) :
    closedPerspective hf 0 0 = 0 := by simp [closedPerspective]

/-- Tonelli integrates the actual nonnegative curvature remainder of measurable densities.
Neither finite total curvature nor finite resulting cost is required. -/
theorem integral_curvatureRemainder (hf : ConvexOn ℝ (Ioi 0) f)
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    {p q : α → ℝ} (hp : Measurable p) (hq : Measurable q) :
    (∫⁻ x, curvatureRemainder hf (p x) (q x) ∂ν) =
      (∫⁻ t in Iic one, (∫⁻ x, ENNReal.ofReal ((t : ℝ) * q x - p x) ∂ν) ∂curvature hf) +
      (∫⁻ t in Ioi one, (∫⁻ x, ENNReal.ofReal (p x - (t : ℝ) * q x) ∂ν) ∂curvature hf) := by
  have hn : Measurable (fun z : α × Positive =>
      ENNReal.ofReal ((z.2 : ℝ) * q z.1 - p z.1)) :=
    ((measurable_subtype_coe.comp measurable_snd).mul (hq.comp measurable_fst) |>.sub
      (hp.comp measurable_fst)).ennreal_ofReal
  have hp' : Measurable (fun z : α × Positive =>
      ENNReal.ofReal (p z.1 - (z.2 : ℝ) * q z.1)) :=
    ((hp.comp measurable_fst).sub
      ((measurable_subtype_coe.comp measurable_snd).mul (hq.comp measurable_fst))).ennreal_ofReal
  simp only [curvatureRemainder]
  rw [lintegral_add_left hn.lintegral_prod_right']
  congr 1
  · exact lintegral_lintegral_swap hn.aemeasurable
  · exact lintegral_lintegral_swap hp'.aemeasurable

/-- The integral of the closed perspective, using its proved finite affine support
and a nonnegative remainder. For nonnegative densities this convention is defined
also at infinite cost and never forms an infinite difference. -/
def closedPerspectiveCost (hf : ConvexOn ℝ (Ioi 0) f)
    {α : Type*} [MeasurableSpace α] (ν : Measure α) (p q : α → ℝ) : EReal :=
  ((∫ x, f 1 * q x + rightDeriv f 1 * (p x - q x) ∂ν : ℝ) : EReal) +
    (∫⁻ x, curvatureRemainder hf (p x) (q x) ∂ν : ℝ≥0∞)

/-- Arbitrary integrable masses retain their finite affine contribution. The
two curvature integrals may be infinite, with no infinite subtraction. -/
theorem closedPerspectiveCost_eq_mass (hf : ConvexOn ℝ (Ioi 0) f)
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    {p q : α → ℝ} (hmp : Measurable p) (hmq : Measurable q)
    (hp : Integrable p ν) (hq : Integrable q ν) :
    closedPerspectiveCost hf ν p q =
      ((f 1 * (∫ x, q x ∂ν) +
        rightDeriv f 1 * ((∫ x, p x ∂ν) - ∫ x, q x ∂ν) : ℝ) : EReal) +
      ((∫⁻ t in Iic one, (∫⁻ x, ENNReal.ofReal ((t : ℝ) * q x - p x) ∂ν) ∂curvature hf) +
        (∫⁻ t in Ioi one, (∫⁻ x, ENNReal.ofReal (p x - (t : ℝ) * q x) ∂ν) ∂curvature hf) : ℝ≥0∞) := by
  have hiq : Integrable (fun x => f 1 * q x) ν := hq.const_mul _
  have hipq : Integrable (fun x => rightDeriv f 1 * (p x - q x)) ν :=
    (hp.sub hq).const_mul _
  rw [closedPerspectiveCost, integral_add hiq hipq,
    integral_const_mul, integral_const_mul, integral_sub hp hq,
    integral_curvatureRemainder hf ν hmp hmq]

/-- For normalized integrable measurable densities, the actual cost is f(1) plus
curvature-integrated hockey-stick costs, including infinite values. The integral is
understood by the finite affine subtraction convention in `closedPerspectiveCost`. -/
theorem closedPerspectiveCost_eq (hf : ConvexOn ℝ (Ioi 0) f)
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    {p q : α → ℝ} (hmp : Measurable p) (hmq : Measurable q)
    (hp : Integrable p ν) (hq : Integrable q ν)
    (hpn : ∫ x, p x ∂ν = 1) (hqn : ∫ x, q x ∂ν = 1) :
    closedPerspectiveCost hf ν p q = (f 1 : EReal) +
      ((∫⁻ t in Iic one, (∫⁻ x, ENNReal.ofReal ((t : ℝ) * q x - p x) ∂ν) ∂curvature hf) +
        (∫⁻ t in Ioi one, (∫⁻ x, ENNReal.ofReal (p x - (t : ℝ) * q x) ∂ν) ∂curvature hf) : ℝ≥0∞) := by
  rw [closedPerspectiveCost_eq_mass hf ν hmp hmq hp hq, hpn, hqn]
  simp only [mul_one, sub_self, mul_zero, add_zero]

#print axioms tendsto_zeroEndpoint
#print axioms tendsto_infinityEndpoint
#print axioms closedPerspective_eq_affine_add_curvature
#print axioms integral_curvatureRemainder
#print axioms closedPerspectiveCost_eq_mass
#print axioms closedPerspectiveCost_eq

end D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
