/- GID: D5/S3/Analytic/Convexity/CurvatureHingeRepresentation
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/CurvatureHingeRepresentation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive-domain convex curvature and the two finite hinge remainders. -/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Continuous
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Layercake

/-! The curvature of a real convex function on the positive ray is constructed from its
right derivative. All integrals used for positive scalar arguments are local. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Analytic.Convexity.CurvatureHingeRepresentation

open Set Filter MeasureTheory
open scoped Topology

/-- The curvature lives on the open positive ray; no finiteness at zero is imposed. -/
abbrev Positive := Ioi (0 : ℝ)

/-- The genuine right derivative, including at nonsmooth points. -/
def rightDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ := derivWithin f (Ioi x) x

variable {f : ℝ → ℝ}

private lemma positive_interior {x : ℝ} (hx : 0 < x) : x ∈ interior (Ioi (0 : ℝ)) := by
  simpa only [interior_Ioi, mem_Ioi] using hx

lemma rightDeriv_monotoneOn (hf : ConvexOn ℝ (Ioi 0) f) :
    MonotoneOn (rightDeriv f) (Ioi 0) := by
  change MonotoneOn (fun x => derivWithin f (Ioi x) x) (Ioi 0)
  simpa only [interior_Ioi] using hf.monotoneOn_rightDeriv

lemma continuousOn_positive (hf : ConvexOn ℝ (Ioi 0) f) : ContinuousOn f (Ioi 0) := by
  simpa only [interior_Ioi] using hf.continuousOn_interior

lemma rightDeriv_right_continuous (hf : ConvexOn ℝ (Ioi 0) f) {x : ℝ} (hx : 0 < x) :
    ContinuousWithinAt (rightDeriv f) (Ici x) x := by
  have hd := hf.hasDerivWithinAt_rightDeriv_of_mem_interior (positive_interior hx)
  have hc : ContinuousAt f x :=
    (continuousOn_positive hf x hx).continuousAt (Ioi_mem_nhds hx)
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ha.trans_le (rightDeriv_monotoneOn hf hx (hx.trans_le hy) hy)
  · intro b hb
    have he : ∀ᶠ z in 𝓝[>] x, x < z ∧ slope f x z < b :=
      (show ∀ᶠ z in 𝓝[>] x, x < z from self_mem_nhdsWithin).and
        (hd.limsup_slope_le' self_notMem_Ioi hb)
    obtain ⟨z, hxz, hzb⟩ := he.exists
    have hs : ContinuousAt (fun y => slope f y z) x := by
      simp only [slope_def_field]
      exact (continuousAt_const.sub hc).div (continuousAt_const.sub continuousAt_id)
        (sub_ne_zero.mpr hxz.ne')
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hxz).filter_mono nhdsWithin_le_nhds,
      (hs.eventually (gt_mem_nhds hzb)).filter_mono nhdsWithin_le_nhds] with y hy hyz hys
    exact (hf.rightDeriv_le_slope_of_mem_interior
      (positive_interior (hx.trans_le hy)) (hx.trans hxz) hyz).trans_lt hys

lemma integral_rightDeriv (hf : ConvexOn ℝ (Ioi 0) f) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in a..b, rightDeriv f x) = f b - f a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
  · exact (continuousOn_positive hf).mono (fun x hx => ha.trans_le hx.1)
  · intro x hx
    exact hf.hasDerivWithinAt_rightDeriv_of_mem_interior (positive_interior (ha.trans hx.1))
  · exact ((rightDeriv_monotoneOn hf).mono (by
      rw [uIcc_of_le hab]
      exact fun x hx => ha.trans_le hx.1)).intervalIntegrable

instance : CompactIccSpace Positive where
  isCompact_Icc {a b} := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    rw [Set.image_subtype_val_Icc]
    exact isCompact_Icc

/-- The Stieltjes function is the actual right derivative, without regularization. -/
def curvatureDistribution (hf : ConvexOn ℝ (Ioi 0) f) : StieltjesFunction Positive where
  toFun x := rightDeriv f x
  mono' x y hxy := rightDeriv_monotoneOn hf x.property y.property hxy
  right_continuous' x := (rightDeriv_right_continuous hf x.property).comp
    continuous_subtype_val.continuousWithinAt (fun _ hy => hy)

/-- Positive locally finite curvature on the positive ray. Its total mass need not be finite. -/
def curvature (hf : ConvexOn ℝ (Ioi 0) f) : Measure Positive :=
  (curvatureDistribution hf).measure

instance curvature_locallyFinite (hf : ConvexOn ℝ (Ioi 0) f) :
    IsLocallyFiniteMeasure (curvature hf) :=
  StieltjesFunction.instIsLocallyFiniteMeasure _

theorem curvature_Ioc (hf : ConvexOn ℝ (Ioi 0) f) (a b : Positive) :
    curvature hf (Ioc a b) = ENNReal.ofReal (rightDeriv f b - rightDeriv f a) :=
  (curvatureDistribution hf).measure_Ioc a b

lemma curvature_real_Ioc (hf : ConvexOn ℝ (Ioi 0) f) {a b : Positive} (hab : a ≤ b) :
    (curvature hf).real (Ioc a b) = rightDeriv f b - rightDeriv f a := by
  rw [measureReal_def, curvature_Ioc, ENNReal.toReal_ofReal]
  exact sub_nonneg.mpr (rightDeriv_monotoneOn hf a.property b.property hab)

private lemma integral_le_indicator {a b t : ℝ} (hat : a < t) (htb : t ≤ b) :
    (∫ x in Ioc a b, if t ≤ x then (1 : ℝ) else 0) = b - t := by
  change (∫ x in Ioc a b, (Ici t).indicator (1 : ℝ → ℝ) x) = _
  rw [integral_indicator_one measurableSet_Ici, measureReal_restrict_apply measurableSet_Ici]
  have he : Ici t ∩ Ioc a b = Icc t b := by
    ext x
    simp only [mem_inter_iff, mem_Ici, mem_Ioc, mem_Icc]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hat.trans_le h.1, h.2⟩⟩
  rw [he, measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr htb)]

private lemma integral_le_indicator_curvature (hf : ConvexOn ℝ (Ioi 0) f)
    (a b : Positive) {x : ℝ} (hx : x ∈ Ioc (a : ℝ) b) :
    (∫ t in Ioc a b, if (t : ℝ) ≤ x then (1 : ℝ) else 0 ∂curvature hf) =
      rightDeriv f x - rightDeriv f a := by
  let c : Positive := ⟨x, a.property.trans hx.1⟩
  change (∫ t in Ioc a b, (Iic c).indicator (1 : Positive → ℝ) t ∂curvature hf) = _
  rw [integral_indicator_one measurableSet_Iic, measureReal_restrict_apply measurableSet_Iic]
  have he : Iic c ∩ Ioc a b = Ioc a c := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hx.2⟩⟩
  rw [he, curvature_real_Ioc hf hx.1.le]

/-- Integrating the indicator of the order triangle is the finite curvature potential.
Only curvature inside `(a,b]` enters the Fubini argument. -/
lemma curvature_potential_eq_integral (hf : ConvexOn ℝ (Ioi 0) f)
    (a b : Positive) (hab : a ≤ b) :
    (∫ t in Ioc a b, ((b : ℝ) - t) ∂curvature hf) =
      ∫ x in (a : ℝ)..b, rightDeriv f x - rightDeriv f a := by
  let μ := (curvature hf).restrict (Ioc a b)
  let ν := volume.restrict (Ioc (a : ℝ) b)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne
  let H : Positive × ℝ → ℝ := fun p => if (p.1 : ℝ) ≤ p.2 then 1 else 0
  have hm : Measurable H := Measurable.ite
    (measurableSet_le (measurable_subtype_coe.comp measurable_fst) measurable_snd)
    measurable_const measurable_const
  have hi : Integrable H (μ.prod ν) := (integrable_const (1 : ℝ)).mono'
    hm.aestronglyMeasurable (Eventually.of_forall fun p => by
      dsimp [H]
      split_ifs <;> norm_num)
  have hs := integral_integral_swap (f := fun (t : Positive) (x : ℝ) => H (t, x)) hi
  change (∫ t, ∫ x, H (t, x) ∂ν ∂μ) = (∫ x, ∫ t, H (t, x) ∂μ ∂ν) at hs
  rw [intervalIntegral.integral_of_le (show (a : ℝ) ≤ b from hab)]
  calc
    (∫ t in Ioc a b, ((b : ℝ) - t) ∂curvature hf) =
        ∫ t, ∫ x, H (t, x) ∂ν ∂μ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      exact (integral_le_indicator ht.1 ht.2).symm
    _ = ∫ x, ∫ t, H (t, x) ∂μ ∂ν := hs
    _ = ∫ x in Ioc (a : ℝ) b, rightDeriv f x - rightDeriv f a := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      exact integral_le_indicator_curvature hf a b hx

theorem scalar_remainder_right (hf : ConvexOn ℝ (Ioi 0) f)
    (a b : Positive) (hab : a ≤ b) :
    f b = f a + rightDeriv f a * ((b : ℝ) - a) +
      ∫ t in Ioc a b, ((b : ℝ) - t) ∂curvature hf := by
  rw [curvature_potential_eq_integral hf a b hab]
  rw [intervalIntegral.integral_sub]
  · rw [integral_rightDeriv hf a.property hab, intervalIntegral.integral_const, smul_eq_mul]
    ring
  · exact ((rightDeriv_monotoneOn hf).mono (by
      rw [uIcc_of_le (show (a : ℝ) ≤ b from hab)]
      exact fun x hx => a.property.trans_le hx.1)).intervalIntegrable
  · exact intervalIntegrable_const

lemma lower_potential_integrable (hf : ConvexOn ℝ (Ioi 0) f) (a b : Positive) :
    IntegrableOn (fun t : Positive => (t : ℝ) - a) (Ioc a b) (curvature hf) :=
  (continuous_subtype_val.sub continuous_const).continuousOn.integrableOn_Icc.mono_set
    Ioc_subset_Icc_self

lemma upper_potential_integrable (hf : ConvexOn ℝ (Ioi 0) f) (a b : Positive) :
    IntegrableOn (fun t : Positive => (b : ℝ) - t) (Ioc a b) (curvature hf) :=
  (continuous_const.sub continuous_subtype_val).continuousOn.integrableOn_Icc.mono_set
    Ioc_subset_Icc_self

/-- The slope at the upper endpoint includes its curvature atom. -/
theorem scalar_remainder_left (hf : ConvexOn ℝ (Ioi 0) f)
    (a b : Positive) (hab : a ≤ b) :
    f a = f b + rightDeriv f b * ((a : ℝ) - b) +
      ∫ t in Ioc a b, ((t : ℝ) - a) ∂curvature hf := by
  have hr := scalar_remainder_right hf a b hab
  have hs : (∫ t in Ioc a b, ((t : ℝ) - a) ∂curvature hf) +
      (∫ t in Ioc a b, ((b : ℝ) - t) ∂curvature hf) =
      ((b : ℝ) - a) * (rightDeriv f b - rightDeriv f a) := by
    rw [← integral_add (lower_potential_integrable hf a b) (upper_potential_integrable hf a b)]
    have he : (fun t : Positive => ((t : ℝ) - a) + ((b : ℝ) - t)) =
        fun _ : Positive => ((b : ℝ) - a) := by funext t; ring
    rw [he, setIntegral_const, curvature_real_Ioc hf hab, smul_eq_mul]
    ring
  nlinarith [hr, hs]

private lemma negative_indicator (a s : Positive) :
    (Iic a).indicator (fun t : Positive => max ((t : ℝ) - s) 0) =
      (Ioc s a).indicator (fun t : Positive => (t : ℝ) - s) := by
  funext t
  by_cases hta : t ≤ a <;> by_cases hst : s < t
  · simp [Set.indicator, hta, hst, max_eq_left (sub_nonneg.mpr hst.le)]
  · simp [Set.indicator, hta, hst, max_eq_right (sub_nonpos.mpr (le_of_not_gt hst))]
  · simp [Set.indicator, hta, hst]
  · simp [Set.indicator, hta, hst]

private lemma positive_indicator (a s : Positive) :
    (Ioi a).indicator (fun t : Positive => max ((s : ℝ) - t) 0) =
      (Ioc a s).indicator (fun t : Positive => (s : ℝ) - t) := by
  funext t
  by_cases hat : a < t <;> by_cases hts : t ≤ s
  · simp [Set.indicator, hat, hts, max_eq_left (sub_nonneg.mpr hts)]
  · simp [Set.indicator, hat, hts, max_eq_right (sub_nonpos.mpr (le_of_not_ge hts).le)]
  · simp [Set.indicator, hat, hts]
  · simp [Set.indicator, hat, hts]

lemma negative_hinge_integrable (hf : ConvexOn ℝ (Ioi 0) f) (a s : Positive) :
    IntegrableOn (fun t : Positive => max ((t : ℝ) - s) 0) (Iic a) (curvature hf) := by
  rw [← integrable_indicator_iff measurableSet_Iic, negative_indicator]
  exact (lower_potential_integrable hf s a).integrable_indicator measurableSet_Ioc

lemma positive_hinge_integrable (hf : ConvexOn ℝ (Ioi 0) f) (a s : Positive) :
    IntegrableOn (fun t : Positive => max ((s : ℝ) - t) 0) (Ioi a) (curvature hf) := by
  rw [← integrable_indicator_iff measurableSet_Ioi, positive_indicator]
  exact (upper_potential_integrable hf a s).integrable_indicator measurableSet_Ioc

/-- The full scalar representation at any positive base point. The negative branch is
closed at the base point, and the positive branch is open there. -/
theorem scalar_hinge_representation (hf : ConvexOn ℝ (Ioi 0) f) (a s : Positive) :
    f s = f a + rightDeriv f a * ((s : ℝ) - a) +
      (∫ t in Iic a, max ((t : ℝ) - s) 0 ∂curvature hf) +
      (∫ t in Ioi a, max ((s : ℝ) - t) 0 ∂curvature hf) := by
  rw [← integral_indicator measurableSet_Iic, negative_indicator,
    integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioi,
    positive_indicator, integral_indicator measurableSet_Ioc]
  rcases le_total s a with hsa | has
  · rw [Ioc_eq_empty_of_le hsa, integral_empty, add_zero]
    exact scalar_remainder_left hf s a hsa
  · rw [Ioc_eq_empty_of_le has, integral_empty, add_zero]
    exact scalar_remainder_right hf a s has

/-- The normalization used for maximal hockey-stick costs. In particular, an atom at one
is integrated in the negative branch. -/
theorem scalar_hinge_at_one (hf : ConvexOn ℝ (Ioi 0) f) (s : ℝ) (hs : 0 < s) :
    f s = f 1 + rightDeriv f 1 * (s - 1) +
      (∫ t in Iic (⟨1, by norm_num⟩ : Positive), max ((t : ℝ) - s) 0 ∂curvature hf) +
      (∫ t in Ioi (⟨1, by norm_num⟩ : Positive), max (s - t) 0 ∂curvature hf) :=
  scalar_hinge_representation hf ⟨1, by norm_num⟩ ⟨s, hs⟩

private lemma scaled_negative_hinge (u v t : ℝ) (hv : 0 < v) :
    v * max (t - u / v) 0 = max (t * v - u) 0 := by
  rw [mul_max_of_nonneg _ _ hv.le, mul_zero]
  congr 1
  field_simp
  ring

private lemma scaled_positive_hinge (u v t : ℝ) (hv : 0 < v) :
    v * max (u / v - t) 0 = max (u - t * v) 0 := by
  rw [mul_max_of_nonneg _ _ hv.le, mul_zero]
  congr 1
  field_simp
  ring

/-- The actual perspective in the open quadrant has the same curvature representation.
This is the scalar identity that is integrated over an actual test. -/
theorem perspective_positive (hf : ConvexOn ℝ (Ioi 0) f) {u v : ℝ}
    (hu : 0 < u) (hv : 0 < v) :
    v * f (u / v) = f 1 * v + rightDeriv f 1 * (u - v) +
      (∫ t in Iic (⟨1, by norm_num⟩ : Positive), max ((t : ℝ) * v - u) 0 ∂curvature hf) +
      (∫ t in Ioi (⟨1, by norm_num⟩ : Positive), max (u - (t : ℝ) * v) 0 ∂curvature hf) := by
  have hn : (∫ t in Iic (⟨1, by norm_num⟩ : Positive),
      max ((t : ℝ) * v - u) 0 ∂curvature hf) =
      v * ∫ t in Iic (⟨1, by norm_num⟩ : Positive),
        max ((t : ℝ) - u / v) 0 ∂curvature hf := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => (scaled_negative_hinge u v t hv).symm
  have hp : (∫ t in Ioi (⟨1, by norm_num⟩ : Positive),
      max (u - (t : ℝ) * v) 0 ∂curvature hf) =
      v * ∫ t in Ioi (⟨1, by norm_num⟩ : Positive),
        max (u / v - t) 0 ∂curvature hf := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => (scaled_positive_hinge u v t hv).symm
  rw [hn, hp, scalar_hinge_at_one hf (u / v) (div_pos hu hv)]
  field_simp
  ring

#print axioms curvature_Ioc
#print axioms scalar_hinge_at_one
#print axioms perspective_positive

end D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
