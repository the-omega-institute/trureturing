/- GID: D5/S3/Analytic/Asymptotics/WeightedFilterTailTransmutation
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/WeightedFilterTailTransmutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A compact probability average of the weighted tail has an exact Laplace formula. -/

import D5.S3.Analytic.Asymptotics.WeightedFilterCDF
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Laplace integral of the unweighted tail primitive

The triangle `0 ≤ v ≤ a` turns a Laplace integral of the upper tail into
an integral against `1 - exp (-y * a)`. Applying this to the translated
input average gives the response of the archived compact correction law.
-/

open MeasureTheory Set

noncomputable section

namespace WeightedFilterTailTransmutation

/-- The upper-tail primitive of an unweighted real signal. -/
def tailPrimitive (r : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ a in Ici v, r a

private theorem integrableOn_exp_neg_mul {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun v : ℝ => Real.exp (-y * v)) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hy) 0

private theorem integral_exp_neg_mul_Icc {y a : ℝ} (hy : 0 < y) (ha : 0 ≤ a) :
    (∫ v in Icc (0 : ℝ) a, Real.exp (-y * v)) = (1 - Real.exp (-y * a)) / y := by
  have hdisj : Disjoint (Icc (0 : ℝ) a) (Ioi a) :=
    (Iic_disjoint_Ioi le_rfl).mono_left Icc_subset_Iic_self
  have hsplit := setIntegral_union hdisj measurableSet_Ioi
    ((integrableOn_exp_neg_mul hy).mono_set Icc_subset_Ici_self)
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hy) a)
  rw [Icc_union_Ioi_eq_Ici ha, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (neg_lt_zero.mpr hy) 0,
    integral_exp_mul_Ioi (neg_lt_zero.mpr hy) a] at hsplit
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq] at hsplit
  rw [sub_div]
  linarith only [hsplit]

/-- The half-line Laplace transform in terms of the upper-tail primitive.
The positive-parameter case uses absolute integrability of the triangular
product, and the zero-parameter case is the definition of the primitive. -/
theorem integral_exp_mul_eq_tailPrimitive {r : ℝ → ℝ} (hrm : Measurable r)
    (hr : IntegrableOn r (Ici 0)) {y : ℝ} (hy : 0 ≤ y) :
    (∫ v in Ici (0 : ℝ), Real.exp (-y * v) * r v) =
      tailPrimitive r 0 - y * (∫ v in Ici (0 : ℝ), Real.exp (-y * v) * tailPrimitive r v) := by
  rcases eq_or_lt_of_le hy with hzero | hy
  · subst y
    simp [tailPrimitive]
  let m := (volume : Measure ℝ).restrict (Ici 0)
  have hhalf : ∀ᵐ v ∂m, v ∈ Ici (0 : ℝ) := ae_restrict_mem measurableSet_Ici
  have he : Integrable (fun v : ℝ => Real.exp (-y * v)) m :=
    integrableOn_exp_neg_mul hy
  let triangle : Set (ℝ × ℝ) := {z | z.1 ≤ z.2}
  have htriangle : MeasurableSet triangle := measurableSet_le measurable_fst measurable_snd
  let f : ℝ → ℝ → ℝ := fun v a =>
    triangle.indicator (fun z => Real.exp (-y * z.1) * r z.2) (v, a)
  have hf : Integrable (Function.uncurry f) (m.prod m) := by
    change Integrable (triangle.indicator (fun z => Real.exp (-y * z.1) * r z.2)) (m.prod m)
    have hr' : Integrable r m := hr
    exact (he.mul_prod hr').indicator htriangle
  have htail_section (v : ℝ) (hv : v ∈ Ici (0 : ℝ)) :
      (∫ a, f v a ∂m) = Real.exp (-y * v) * tailPrimitive r v := by
    have hpre : (fun a : ℝ => (v, a)) ⁻¹' triangle = Ici v := rfl
    simp_rw [f, ← indicator_comp_right (fun a : ℝ => (v, a)), hpre,
      integral_indicator measurableSet_Ici]
    change (∫ a, Real.exp (-y * v) * r a ∂(m.restrict (Ici v))) = _
    have hre : m.restrict (Ici v) = (volume : Measure ℝ).restrict (Ici v) :=
      Measure.restrict_restrict_of_subset (Ici_subset_Ici.mpr (mem_Ici.mp hv))
    rw [hre, integral_const_mul, tailPrimitive]
  have hexp_section (a : ℝ) (ha : a ∈ Ici (0 : ℝ)) :
      (∫ v, f v a ∂m) = ((1 - Real.exp (-y * a)) / y) * r a := by
    have hpre : (fun v : ℝ => (v, a)) ⁻¹' triangle = Iic a := rfl
    simp_rw [f, ← indicator_comp_right (fun v : ℝ => (v, a)), hpre]
    change (∫ v in Ici (0 : ℝ), (Iic a).indicator (fun v => Real.exp (-y * v) * r a) v) = _
    rw [setIntegral_indicator measurableSet_Iic, Ici_inter_Iic, integral_mul_const,
      integral_exp_neg_mul_Icc hy (mem_Ici.mp ha)]
  have hswap :
      (∫ v, Real.exp (-y * v) * tailPrimitive r v ∂m) =
        ∫ a, ((1 - Real.exp (-y * a)) / y) * r a ∂m := by
    calc
      _ = ∫ v, ∫ a, f v a ∂m ∂m :=
        integral_congr_ae (hhalf.mono fun v hv => (htail_section v hv).symm)
      _ = ∫ a, ∫ v, f v a ∂m ∂m := integral_integral_swap hf
      _ = _ := integral_congr_ae (hhalf.mono fun a ha => hexp_section a ha)
  have hr_exp : Integrable (fun a => Real.exp (-y * a) * r a) m := by
    have hr' : Integrable r m := hr
    apply hr'.mono (he.aestronglyMeasurable.mul hrm.aestronglyMeasurable)
    filter_upwards [hhalf] with a ha
    have hle : Real.exp (-y * a) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hy.le) ha)
    change ‖Real.exp (-y * a) * r a‖ ≤ ‖r a‖
    rw [norm_mul, Real.norm_eq_abs (Real.exp (-y * a)), abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (norm_nonneg _) hle
  have hdiff :
      y * (∫ v, Real.exp (-y * v) * tailPrimitive r v ∂m) =
        tailPrimitive r 0 - (∫ a, Real.exp (-y * a) * r a ∂m) := by
    rw [hswap, ← integral_const_mul, tailPrimitive, ← integral_sub hr hr_exp]
    apply integral_congr_ae
    exact ae_of_all _ (fun a => by
      field_simp [hy.ne'] <;> ring)
  change (∫ v, Real.exp (-y * v) * r v ∂m) =
    tailPrimitive r 0 - y * (∫ v, Real.exp (-y * v) * tailPrimitive r v ∂m)
  rw [hdiff]
  ring

open WeightedFilterCDF

private theorem measurable_moment (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (moment μ) := by
  have hm : Measurable (fun z : ℝ × ℝ => Real.exp (z.1 * z.2)) := by fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

private theorem one_le_moment {μ : Measure ℝ} [IsProbabilityMeasure μ] {h y : ℝ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (hy : 0 ≤ y) :
    1 ≤ moment μ y := by
  have hint : Integrable (fun u => Real.exp (y * u)) μ := by
    apply Integrable.of_bound (by fun_prop) (Real.exp (y * h))
    filter_upwards [hμ] with u hu
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu.2 hy)
  calc
    1 = ∫ _u, (1 : ℝ) ∂μ := by simp
    _ ≤ moment μ y := by
      apply integral_mono_ae (integrable_const _) hint
      filter_upwards [hμ] with u hu
      exact Real.one_le_exp (mul_nonneg hy hu.1)

/-- The Laplace density is integrable on the nonnegative half-line. -/
theorem integrableOn_laplace_density {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun y : ℝ => (1 + y) * Real.exp (-t * y)) (Ici 0) := by
  have hfirst : IntegrableOn (fun y : ℝ => y * Real.exp (-t * y)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1 : ℝ)) (s := (1 : ℝ))
        (by norm_num) (by norm_num) ht
  have hsum : (fun y : ℝ => (1 + y) * Real.exp (-t * y)) =
      (fun y : ℝ => Real.exp (-t * y)) + (fun y => y * Real.exp (-t * y)) := by
    funext y
    simp only [Pi.add_apply, add_mul, one_mul]
  rw [hsum]
  exact (integrableOn_exp_neg_mul ht).add hfirst

/-- The compact positive correction law
pairs the weighted upper tail with the Laplace response of the forward average
of the unweighted primitive. The density of the half-line Laplace measure is
written explicitly. -/
theorem exists_compact_probability_weighted_tail_average_eq_laplace
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {h t : ℝ}
    (hμ : ∀ᵐ u ∂μ, u ∈ Icc 0 h) (ht : 0 < t) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Icc 0 h)ᶜ = 0 ∧
      ∀ (r : ℝ → ℝ), Measurable r → IntegrableOn r (Ici t) →
        (∫ u, (∫ a in Ici (t + u), weight a * r a) ∂ν) =
          ∫ y in Ici (0 : ℝ), ((1 + y) * Real.exp (-t * y) / moment μ y) *
            ((∫ u, tailPrimitive r (t + u) ∂μ) -
              y * (∫ v in Ici (0 : ℝ), Real.exp (-y * v) *
                (∫ u, tailPrimitive r (t + v + u) ∂μ))) := by
  obtain ⟨ν, hprob, hsupp, hweighted⟩ := exists_compact_probability_weighted_tail_average hμ ht
  refine ⟨ν, hprob, hsupp, ?_⟩
  intro r hrm hr
  let m := (volume : Measure ℝ).restrict (Ici 0)
  have hhalf : ∀ᵐ v ∂m, v ∈ Ici (0 : ℝ) := ae_restrict_mem measurableSet_Ici
  let avg : ℝ → ℝ := fun v => ∫ u, r (t + v + u) ∂μ
  let shifted : ℝ → ℝ → ℝ := fun u a => r (t + a + u)
  have hshifted : Measurable (Function.uncurry shifted) := by
    exact hrm.comp (show Measurable (fun z : ℝ × ℝ => t + z.2 + z.1) by fun_prop)
  have havgm : Measurable avg :=
    (hshifted.stronglyMeasurable.integral_prod_left (μ := μ)).measurable
  have htranslate (v u : ℝ) :
      MeasurePreserving (fun a : ℝ => a + (t + u))
        (volume.restrict (Ici v)) (volume.restrict (Ici (t + v + u))) := by
    have hpre : (fun a : ℝ => a + (t + u)) ⁻¹' Ici (t + v + u) = Ici v := by
      ext a
      change t + v + u ≤ a + (t + u) ↔ v ≤ a
      constructor <;> intro ha <;> linarith
    have he := (measurePreserving_add_right (volume : Measure ℝ) (t + u)).restrict_preimage
      (measurableSet_Ici (a := t + v + u))
    rw [hpre] at he
    exact he
  have hintegral_translate (g : ℝ → ℝ) (hgm : Measurable g) (v u : ℝ) :
      (∫ a in Ici v, g (t + a + u)) = ∫ a in Ici (t + v + u), g a := by
    calc
      _ = ∫ a in Ici v, g (a + (t + u)) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun a => congrArg g (by ring))
      _ = _ := by
        rw [← (htranslate v u).map_eq]
        exact (integral_map_of_stronglyMeasurable (htranslate v u).measurable
          hgm.stronglyMeasurable).symm
  have hshifted_integrable (v : ℝ) (hv : 0 ≤ v) :
      Integrable (Function.uncurry shifted) (μ.prod (volume.restrict (Ici v))) := by
    apply (integrable_prod_iff hshifted.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [hμ] with u hu
      have hstart : t ≤ t + v + u := by linarith [hu.1]
      have hlocal := hr.mono_set (Ici_subset_Ici.mpr hstart)
      have hcomp := (htranslate v u).integrable_comp_of_integrable hlocal
      change Integrable (fun a => r (a + (t + u))) (volume.restrict (Ici v)) at hcomp
      change Integrable (fun a => r (t + a + u)) (volume.restrict (Ici v))
      simpa only [add_assoc, add_left_comm, add_comm] using hcomp
    · have hmeas := hshifted.stronglyMeasurable.norm.integral_prod_right'
        (ν := volume.restrict (Ici v))
      apply Integrable.of_bound hmeas.aestronglyMeasurable (∫ a in Ici t, ‖r a‖)
      filter_upwards [hμ] with u hu
      change ‖(∫ a in Ici v, ‖r (t + a + u)‖)‖ ≤ ∫ a in Ici t, ‖r a‖
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _)),
        hintegral_translate (fun a => ‖r a‖) hrm.norm v u]
      have hstart : t ≤ t + v + u := by linarith [hu.1]
      exact setIntegral_mono_set hr.norm (ae_of_all _ (fun _ => norm_nonneg _))
        (Ici_subset_Ici.mpr hstart).eventuallySubset
  have havgi : IntegrableOn avg (Ici 0) := (hshifted_integrable 0 le_rfl).integral_prod_right
  have havg_tail (v : ℝ) (hv : 0 ≤ v) :
      tailPrimitive avg v = ∫ u, tailPrimitive r (t + v + u) ∂μ := by
    calc
      _ = ∫ a in Ici v, ∫ u, shifted u a ∂μ := rfl
      _ = ∫ u, (∫ a in Ici v, shifted u a) ∂μ :=
        (integral_integral_swap (hshifted_integrable v hv)).symm
      _ = _ := integral_congr_ae (ae_of_all _ (fun u => hintegral_translate r hrm v u))
  let density : ℝ → ℝ := fun y => (1 + y) * Real.exp (-t * y)
  let f : ℝ → ℝ → ℝ := fun v y =>
    density y / moment μ y * (Real.exp (-y * v) * avg v)
  have hf_m : Measurable (Function.uncurry f) := by
    have hd : Measurable density := by
      unfold density
      fun_prop
    exact ((hd.comp measurable_snd).div
      ((measurable_moment μ).comp measurable_snd)).mul
      ((show Measurable (fun z : ℝ × ℝ => Real.exp (-z.2 * z.1)) by fun_prop).mul
        (havgm.comp measurable_fst))
  have hprod_mem : ∀ᵐ z ∂m.prod m, z ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) := by
    apply (Measure.ae_prod_mem_iff_ae_ae_mem (measurableSet_Ici.prod measurableSet_Ici)).mpr
    filter_upwards [hhalf] with v hv
    filter_upwards [hhalf] with y hy
    exact ⟨hv, hy⟩
  have hf : Integrable (Function.uncurry f) (m.prod m) := by
    have hdom : Integrable (fun z : ℝ × ℝ => ‖avg z.1‖ * density z.2) (m.prod m) := by
      exact havgi.norm.mul_prod (integrableOn_laplace_density ht)
    apply hdom.mono' hf_m.aestronglyMeasurable
    filter_upwards [hprod_mem] with z hz
    obtain ⟨hv, hy⟩ := Set.mem_prod.mp hz
    have hM := one_le_moment hμ (mem_Ici.mp hy)
    have hMpos : 0 < moment μ z.2 := zero_lt_one.trans_le hM
    have hd : 0 ≤ density z.2 := by
      dsimp only [density]
      exact mul_nonneg (by linarith [mem_Ici.mp hy]) (Real.exp_pos _).le
    have hcoeff : density z.2 / moment μ z.2 ≤ density z.2 := by
      apply (div_le_iff₀ hMpos).mpr
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hM hd
    have hev : Real.exp (-z.2 * z.1) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mem_Ici.mp hy)) (mem_Ici.mp hv))
    change ‖density z.2 / moment μ z.2 * (Real.exp (-z.2 * z.1) * avg z.1)‖ ≤
      ‖avg z.1‖ * density z.2
    rw [norm_mul (density z.2 / moment μ z.2), norm_mul (Real.exp (-z.2 * z.1)),
      Real.norm_eq_abs (density z.2 / moment μ z.2),
      abs_of_nonneg (div_nonneg hd hMpos.le), Real.norm_eq_abs (Real.exp (-z.2 * z.1)),
      abs_of_pos (Real.exp_pos _), mul_comm ‖avg z.1‖ (density z.2)]
    exact mul_le_mul hcoeff (mul_le_of_le_one_left (norm_nonneg _) hev)
      (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) hd
  have hkernel (v : ℝ) :
      kernel μ (t + v) * avg v = ∫ y, f v y ∂m := by
    rw [kernel_eq_integral_Ici, ← integral_mul_const]
    apply integral_congr_ae
    apply ae_of_all
    intro y
    change (1 + y) * Real.exp (-(t + v) * y) / moment μ y * avg v =
      ((1 + y) * Real.exp (-t * y) / moment μ y) * (Real.exp (-y * v) * avg v)
    rw [show -(t + v) * y = -t * y + -y * v by ring, Real.exp_add]
    ring
  rw [hweighted r hrm hr]
  change (∫ v, kernel μ (t + v) * avg v ∂m) = _
  calc
    _ = ∫ v, ∫ y, f v y ∂m ∂m := integral_congr_ae (ae_of_all _ hkernel)
    _ = ∫ y, ∫ v, f v y ∂m ∂m := integral_integral_swap hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hhalf] with y hy
      have htail_int :
          (∫ v in Ici (0 : ℝ), Real.exp (-y * v) * tailPrimitive avg v) =
            ∫ v in Ici (0 : ℝ), Real.exp (-y * v) *
              (∫ u, tailPrimitive r (t + v + u) ∂μ) := by
        apply integral_congr_ae
        filter_upwards [hhalf] with v hv
        rw [havg_tail v (mem_Ici.mp hv)]
      simp only [f, integral_const_mul, density]
      rw [integral_exp_mul_eq_tailPrimitive havgm havgi (mem_Ici.mp hy), havg_tail 0 le_rfl,
        add_zero, htail_int]

end WeightedFilterTailTransmutation
