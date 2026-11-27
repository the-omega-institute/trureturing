/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Round sphere measure, dot-product distribution and angular logarithmic integrability. -/

import OmegaBuild.Commands
import D5.S3.Arith.Robin.ForwardKernel.ClippedLogEnergy
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Round angular measure for the four-dimensional null cone. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace Pointwise

namespace NullConeGravity

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev Sphere4D := sphere (0 : E3) 1

/-- Haar angular measure on the unit sphere in three Euclidean dimensions. -/
def sphereMeasure : Measure Sphere4D := (volume : Measure E3).toSphere

instance sphereMeasure_isFinite : IsFiniteMeasure sphereMeasure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure E3).toSphere))

abbrev Phase4D := ℝ × Sphere4D

/-- Lebesgue measure in frequency times the round angular measure. -/
def phaseMeasure : Measure Phase4D := (volume : Measure ℝ).prod sphereMeasure

abbrev H4D := Lp ℂ 2 phaseMeasure

/-- Euclidean dot product of two unit directions. -/
def sphereDot (n n' : Sphere4D) : ℝ := ⟪(n : E3), (n' : E3)⟫_ℝ

private theorem measurable_sphereDot (n : Sphere4D) : Measurable (sphereDot n) := by
  unfold sphereDot
  fun_prop

private theorem continuous_sphereDot_prod :
    Continuous (fun p : Sphere4D × Sphere4D ↦ sphereDot p.1 p.2) := by
  unfold sphereDot
  fun_prop

theorem sphere_measure_univ : sphereMeasure univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [sphereMeasure, Measure.toSphere_apply_univ, EuclideanSpace.volume_ball_fin_three]
  calc
    _ = ENNReal.ofReal (3 * (Real.pi * 4 / 3)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    _ = _ := by
      congr 1
      ring

private theorem norm_direction (n : Sphere4D) : ‖(n : E3)‖ = 1 := by
  simp

private abbrev E2 := EuclideanSpace ℝ (Fin 2)
private abbrev HeightSpace := WithLp 2 (ℝ × E2)

private theorem norm_height_sq (z : ℝ) (y : E2) :
    ‖WithLp.toLp 2 (z, y)‖ ^ 2 = z ^ 2 + ‖y‖ ^ 2 := by
  simp [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

private def heightIsometry (n : Sphere4D) : E3 ≃ₗᵢ[ℝ] HeightSpace := by
  have hdim : Module.finrank ℝ HeightSpace = 3 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × E2)).finrank_eq, Module.finrank_prod]
    simp
  let e : E3 ≃ₗᵢ[ℝ] HeightSpace :=
    ((stdOrthonormalBasis ℝ HeightSpace).reindex (finCongr hdim)).repr.symm
  let pole : E3 := e.symm (WithLp.toLp 2 ((1 : ℝ), (0 : E2)))
  exact ((ℝ ∙ ((n : E3) - pole))ᗮ.reflection).trans e

private theorem heightIsometry_pole (n : Sphere4D) :
    heightIsometry n n = WithLp.toLp 2 ((1 : ℝ), (0 : E2)) := by
  unfold heightIsometry
  rw [LinearIsometryEquiv.trans_apply, Submodule.reflection_sub]
  · simp
  · rw [norm_direction, LinearIsometryEquiv.norm_map,
      ← sq_eq_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _), norm_height_sq]
    simp

private theorem heightIsometry_fst (n : Sphere4D) (v : E3) :
    (WithLp.ofLp (heightIsometry n v)).1 = ⟪(n : E3), v⟫_ℝ := by
  rw [← (heightIsometry n).inner_map_map, heightIsometry_pole]
  simp

private def solidCap (c : ℝ) : Set (ℝ × E2) :=
  {p | ‖WithLp.toLp 2 p‖ < 1 ∧ c * ‖WithLp.toLp 2 p‖ < p.1}

private theorem measurableSet_solidCap (c : ℝ) : MeasurableSet (solidCap c) := by
  have hm : Measurable (fun p : ℝ × E2 ↦ ‖WithLp.toLp 2 p‖) :=
    continuous_norm.measurable.comp (MeasurableEquiv.toLp 2 _).measurable
  exact (measurableSet_lt hm measurable_const).inter
    (measurableSet_lt (measurable_const.mul hm) measurable_fst)

private theorem cone_eq_preimage (n : Sphere4D) (c : ℝ) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphereDot n ⁻¹' Ioi c)) =
      (WithLp.ofLp ∘ heightIsometry n) ⁻¹' solidCap c := by
  ext v
  change _ ↔ ‖heightIsometry n v‖ < 1 ∧
    c * ‖heightIsometry n v‖ < (WithLp.ofLp (heightIsometry n v)).1
  rw [(heightIsometry n).norm_map, heightIsometry_fst]
  constructor
  · rintro ⟨r, ⟨hr₀, hr₁⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr₀, norm_direction, mul_one,
      real_inner_smul_right]
    exact ⟨hr₁, by simpa [mul_comm, sphereDot] using (mul_lt_mul_of_pos_left hw hr₀)⟩
  · rintro ⟨h₁, hc⟩
    have hv : ‖v‖ ≠ 0 := by
      intro h
      simp [norm_eq_zero.mp h] at hc
    let w : Sphere4D := ⟨‖v‖⁻¹ • v, by
      simp [norm_smul, hv]⟩
    refine ⟨‖v‖, ⟨lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv), h₁⟩, w, ⟨w, ?_, rfl⟩, ?_⟩
    · change c < ⟪(n : E3), ‖v‖⁻¹ • v⟫_ℝ
      rw [real_inner_smul_right, ← div_eq_inv_mul]
      exact (lt_div_iff₀ (lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv))).2 hc
    · simp [w, smul_smul, hv]

private theorem volume_disk (q : ℝ) (hq : 0 ≤ q) :
    (volume : Measure E2) {y | ‖y‖ ^ 2 < q} = ENNReal.ofReal (Real.pi * q) := by
  have hs : {y : E2 | ‖y‖ ^ 2 < q} = ball 0 (Real.sqrt q) := by
    ext y
    simp [mem_ball, dist_zero_right, Real.lt_sqrt (norm_nonneg y)]
  rw [hs, EuclideanSpace.volume_ball_fin_two,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hq, mul_comm,
    ← ENNReal.ofReal_mul Real.pi_pos.le]

-- Below height c the cone limits the disk radius. Above c the unit ball limits it.
private theorem solidCap_fibres (c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (z : ℝ) :
    (volume : Measure E2) (Prod.mk z ⁻¹' solidCap c) =
      (Ioc 0 c).indicator (fun t : ℝ ↦ ENNReal.ofReal (Real.pi * (1 - c ^ 2) / c ^ 2 * t ^ 2)) z +
      (Ioc c 1).indicator (fun t : ℝ ↦ ENNReal.ofReal (Real.pi * (1 - t ^ 2))) z := by
  have hnorm : ∀ y : E2, 0 ≤ ‖WithLp.toLp 2 (z, y)‖ := fun _ ↦ norm_nonneg _
  by_cases hlow : z ∈ Ioc 0 c
  · have hz₀ : 0 < z := hlow.1
    have hzc : z ≤ c := hlow.2
    have hc : 0 < c := hz₀.trans_le hzc
    have hc_sq : 0 < c ^ 2 := by positivity
    have hc_sq_le : c ^ 2 ≤ 1 := by nlinarith
    have hupp : z ∉ Ioc c 1 := fun hz ↦ hz.1.not_ge hzc
    rw [indicator_of_mem hlow, indicator_of_notMem hupp, add_zero]
    have hfibre : Prod.mk z ⁻¹' solidCap c = {y : E2 | ‖y‖ ^ 2 < (1 - c ^ 2) / c ^ 2 * z ^ 2} := by
      ext y
      change (‖WithLp.toLp 2 (z, y)‖ < 1 ∧ c * ‖WithLp.toLp 2 (z, y)‖ < z) ↔ _
      have hcone : c * ‖WithLp.toLp 2 (z, y)‖ < z ↔
          ‖y‖ ^ 2 < (1 - c ^ 2) / c ^ 2 * z ^ 2 := by
        rw [← sq_lt_sq₀ (mul_nonneg hc₀ (hnorm y)) hz₀.le, mul_pow, norm_height_sq]
        rw [div_mul_eq_mul_div, lt_div_iff₀ hc_sq]
        have hL : c ^ 2 * (z ^ 2 + ‖y‖ ^ 2) = c ^ 2 * z ^ 2 + ‖y‖ ^ 2 * c ^ 2 := by ring
        have hR : (1 - c ^ 2) * z ^ 2 = z ^ 2 - c ^ 2 * z ^ 2 := by ring
        constructor <;> intro h <;> linarith only [h, hL, hR]
      rw [hcone]
      refine ⟨And.right, fun h ↦ ⟨?_, h⟩⟩
      have h' := hcone.mpr h
      have hlt : c * ‖WithLp.toLp 2 (z, y)‖ < c * 1 := by linarith
      exact lt_of_mul_lt_mul_left hlt hc₀
    rw [hfibre, volume_disk _ (by positivity)]
    congr 1
    ring
  · rw [indicator_of_notMem hlow, zero_add]
    by_cases hupp : z ∈ Ioc c 1
    · have hz₀ : 0 ≤ z := hc₀.trans hupp.1.le
      have hz₁ : z ≤ 1 := hupp.2
      rw [indicator_of_mem hupp]
      have hfibre : Prod.mk z ⁻¹' solidCap c = {y : E2 | ‖y‖ ^ 2 < 1 - z ^ 2} := by
        ext y
        change (‖WithLp.toLp 2 (z, y)‖ < 1 ∧ c * ‖WithLp.toLp 2 (z, y)‖ < z) ↔ _
        have hball : ‖WithLp.toLp 2 (z, y)‖ < 1 ↔ ‖y‖ ^ 2 < 1 - z ^ 2 := by
          rw [← sq_lt_sq₀ (hnorm y) (by norm_num : (0 : ℝ) ≤ 1), norm_height_sq]
          constructor <;> intro h <;> linarith
        exact ⟨fun h ↦ hball.mp h.1, fun h ↦ ⟨hball.mpr h,
          (mul_le_of_le_one_right hc₀ (hball.mpr h).le).trans_lt hupp.1⟩⟩
      rw [hfibre, volume_disk _ (by nlinarith)]
    · rw [indicator_of_notMem hupp]
      have hempty : Prod.mk z ⁻¹' solidCap c = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        change ‖WithLp.toLp 2 (z, y)‖ < 1 ∧ c * ‖WithLp.toLp 2 (z, y)‖ < z at hy
        have hz₀ := (mul_nonneg hc₀ (hnorm y)).trans_lt hy.2
        have hz₁ : z ≤ 1 := by
          have hn := (sq_lt_sq₀ (hnorm y) (by norm_num : (0 : ℝ) ≤ 1)).2 hy.1
          rw [norm_height_sq] at hn
          nlinarith [sq_nonneg ‖y‖]
        exact hupp ⟨lt_of_not_ge (fun hz ↦ hlow ⟨hz₀, hz⟩), hz₁⟩
      rw [hempty, measure_empty]

private theorem volume_solidCap (c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    (volume : Measure (ℝ × E2)) (solidCap c) =
      ENNReal.ofReal (2 * Real.pi * (1 - c) / 3) := by
  have hc_sq_le : c ^ 2 ≤ 1 := by nlinarith
  let a : ℝ := Real.pi * (1 - c ^ 2) / c ^ 2
  have ha : 0 ≤ a := by positivity
  have h₁ : IntervalIntegrable (fun t : ℝ ↦ a * t ^ 2) volume 0 c :=
    (show Continuous (fun t : ℝ ↦ a * t ^ 2) by fun_prop).intervalIntegrable ..
  have h₂ : IntervalIntegrable (fun t : ℝ ↦ Real.pi * (1 - t ^ 2)) volume c 1 :=
    (show Continuous (fun t : ℝ ↦ Real.pi * (1 - t ^ 2)) by fun_prop).intervalIntegrable ..
  change ((volume : Measure ℝ).prod (volume : Measure E2)) (solidCap c) = _
  rw [Measure.prod_apply (measurableSet_solidCap c)]
  simp_rw [solidCap_fibres c hc₀ hc₁]
  rw [lintegral_add_left, lintegral_indicator measurableSet_Ioc,
    lintegral_indicator measurableSet_Ioc]
  · rw [← ofReal_integral_eq_lintegral_ofReal h₁.1,
      ← ofReal_integral_eq_lintegral_ofReal h₂.1,
      ← intervalIntegral.integral_of_le hc₀, ← intervalIntegral.integral_of_le hc₁,
      ← ENNReal.ofReal_add]
    · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub intervalIntegrable_const
          (show IntervalIntegrable (fun x : ℝ ↦ x ^ 2) volume c 1 from
            (continuous_id.pow 2).intervalIntegrable ..),
        intervalIntegral.integral_const, integral_pow 2, integral_pow 2]
      simp [a]
      congr 1
      by_cases hc : c = 0
      · simp [hc]
        ring
      · field_simp
        ring
    · exact intervalIntegral.integral_nonneg hc₀ fun t _ ↦ by positivity
    · exact intervalIntegral.integral_nonneg hc₁ fun t ht ↦
        mul_nonneg Real.pi_pos.le (by nlinarith [ht.1, ht.2])
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg Real.pi_pos.le (by nlinarith [ht.1, ht.2])
    · exact Filter.Eventually.of_forall fun t ↦ mul_nonneg ha (sq_nonneg t)
  · apply Measurable.indicator _ measurableSet_Ioc
    fun_prop

private theorem sphere_cap_eq_solid (n : Sphere4D) (c : ℝ) :
    Measure.map (sphereDot n) sphereMeasure (Ioi c) =
      3 * (volume : Measure (ℝ × E2)) (solidCap c) := by
  rw [Measure.map_apply (measurable_sphereDot n) measurableSet_Ioi, sphereMeasure,
    Measure.toSphere_apply' _ ((measurable_sphereDot n) measurableSet_Ioi),
    cone_eq_preimage]
  have hmp : MeasurePreserving (WithLp.ofLp ∘ heightIsometry n) :=
    (WithLp.volume_preserving_ofLp _ _).comp (heightIsometry n).measurePreserving
  rw [hmp.measure_preimage (measurableSet_solidCap c).nullMeasurableSet]
  norm_num

private theorem sphere_cap (n : Sphere4D) (c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    Measure.map (sphereDot n) sphereMeasure (Ioi c) = ENNReal.ofReal (2 * Real.pi * (1 - c)) := by
  rw [sphere_cap_eq_solid, volume_solidCap c hc₀ hc₁]
  calc
    _ = ENNReal.ofReal (3 * (2 * Real.pi * (1 - c) / 3)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    _ = _ := by
      congr 1
      ring

private theorem measure_eq_of_upper_tails {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    (huniv : μ univ = ν univ) (htails : ∀ c : ℝ, μ (Ioi c) = ν (Ioi c)) : μ = ν := by
  refine Measure.ext_of_generateFrom_of_cover
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ))
    (countable_singleton univ) isPiSystem_Ioi (by simp)
    (fun t _ ↦ measure_ne_top μ t) ?_ ?_
  · rintro t (rfl : t = univ) _ ⟨c, rfl⟩
    simpa using htails c
  · simpa using huniv

private def dotTarget : Measure ℝ :=
  ENNReal.ofReal (2 * Real.pi) • volume.restrict (Icc (-1 : ℝ) 1)

private theorem dotTarget_univ : dotTarget univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [dotTarget, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc,
    smul_eq_mul, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
  congr 1
  ring

private theorem map_sphereDot_univ (n : Sphere4D) :
    (Measure.map (sphereDot n) sphereMeasure) univ = ENNReal.ofReal (4 * Real.pi) := by
  rw [Measure.map_apply (measurable_sphereDot n) MeasurableSet.univ, preimage_univ,
    sphere_measure_univ]

private theorem dot_upper_tail (n : Sphere4D) (c : ℝ) (hc : 0 ≤ c) :
    Measure.map (sphereDot n) sphereMeasure (Ioi c) = dotTarget (Ioi c) := by
  by_cases h₁ : c ≤ 1
  · have hset : Ioi c ∩ Icc (-1 : ℝ) 1 = Ioc c 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
      constructor
      · exact fun h ↦ ⟨h.1, h.2.2⟩
      · exact fun h ↦ ⟨h.1, by linarith [h.1], h.2⟩
    rw [sphere_cap n c hc h₁, dotTarget, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Ioi, hset, Real.volume_Ioc, smul_eq_mul,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
  · have hset : Ioi c ∩ Icc (-1 : ℝ) 1 = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx ↦ h₁ (hx.1.le.trans hx.2.2)
    have hpre : sphereDot n ⁻¹' Ioi c = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hb := real_inner_le_norm (n : E3) (w : E3)
      rw [norm_direction, norm_direction, mul_one] at hb
      exact h₁ ((show c < sphereDot n w from hw).le.trans hb)
    rw [Measure.map_apply (measurable_sphereDot n) measurableSet_Ioi, hpre, dotTarget,
      Measure.smul_apply, Measure.restrict_apply measurableSet_Ioi, hset, measure_empty,
      measure_empty, smul_zero]

private theorem map_neg_dotTarget : dotTarget.map (fun x : ℝ ↦ -x) = dotTarget := by
  unfold dotTarget
  let e := MeasurableEquiv.neg ℝ
  have hpre : e ⁻¹' Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 1 := by
    ext x
    change (-1 ≤ -x ∧ -x ≤ 1) ↔ (-1 ≤ x ∧ x ≤ 1)
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hmap : Measure.map e ((volume : Measure ℝ).restrict (Icc (-1) 1)) =
      (Measure.map e volume).restrict (Icc (-1) 1) := by
    rw [e.measurableEmbedding.restrict_map, hpre]
  rw [Measure.map_smul _ measurable_neg.aemeasurable]
  change ENNReal.ofReal (2 * Real.pi) • Measure.map e _ = _
  rw [hmap]
  exact congrArg (fun ρ : Measure ℝ ↦ ENNReal.ofReal (2 * Real.pi) • ρ.restrict (Icc (-1) 1))
    (Measure.map_neg_eq_self volume)

-- The same solid cap computes the upper tail for every axis, including the opposite axis.
private theorem map_neg_sphereDot (n : Sphere4D) :
    (Measure.map (sphereDot n) sphereMeasure).map (fun x : ℝ ↦ -x) =
      Measure.map (sphereDot n) sphereMeasure := by
  let m : Sphere4D := ⟨-(n : E3), by simp⟩
  have hneg : (fun x : ℝ ↦ -x) ∘ sphereDot n = sphereDot m := by
    funext w
    simp [sphereDot, m]
  rw [Measure.map_map measurable_neg (measurable_sphereDot n), hneg]
  have hfinite := sphereMeasure.isFiniteMeasure_map (sphereDot m)
  exact measure_eq_of_upper_tails (by rw [map_sphereDot_univ, map_sphereDot_univ])
    (fun c ↦ by rw [sphere_cap_eq_solid, sphere_cap_eq_solid])

/-- The dot product with a fixed unit direction has density `2 * Real.pi` on the interval
from minus one to one. -/
theorem sphere_dot_pushforward (n : Sphere4D) :
    Measure.map (sphereDot n) sphereMeasure =
      ENNReal.ofReal (2 * Real.pi) • volume.restrict (Icc (-1 : ℝ) 1) := by
  change Measure.map (sphereDot n) sphereMeasure = dotTarget
  let μ := Measure.map (sphereDot n) sphereMeasure
  change μ = dotTarget
  have hfinite : IsFiniteMeasure μ := sphereMeasure.isFiniteMeasure_map (sphereDot n)
  have huniv : μ univ = dotTarget univ := by rw [dotTarget_univ, map_sphereDot_univ]
  have hpos : μ.restrict (Ioi 0) = dotTarget.restrict (Ioi 0) := by
    refine measure_eq_of_upper_tails ?_ (fun c ↦ ?_)
    · rw [Measure.restrict_apply_univ, Measure.restrict_apply_univ]
      exact dot_upper_tail n 0 le_rfl
    · rw [Measure.restrict_apply measurableSet_Ioi, Measure.restrict_apply measurableSet_Ioi,
        Ioi_inter_Ioi]
      exact dot_upper_tail n _ (le_max_right _ _)
  refine measure_eq_of_upper_tails huniv fun c ↦ ?_
  by_cases hc : 0 ≤ c
  · exact dot_upper_tail n c hc
  · have hc' : 0 < -c := by linarith
    have hset : (fun x : ℝ ↦ -x) ⁻¹' Ici (-c) = (Ioi c)ᶜ := by
      ext x
      simp
    have hμ : μ ((Ioi c)ᶜ) = μ (Ici (-c)) := by
      rw [← hset, ← Measure.map_apply measurable_neg measurableSet_Ici, map_neg_sphereDot]
    have hν : dotTarget ((Ioi c)ᶜ) = dotTarget (Ici (-c)) := by
      rw [← hset, ← Measure.map_apply measurable_neg measurableSet_Ici, map_neg_dotTarget]
    have hrestrict : Ici (-c) ∩ Ioi 0 = Ici (-c) :=
      inter_eq_left.mpr fun _ hx ↦ hc'.trans_le hx
    have hclosed : μ (Ici (-c)) = dotTarget (Ici (-c)) := by
      have h := congrArg (fun ρ : Measure ℝ ↦ ρ (Ici (-c))) hpos
      rwa [Measure.restrict_apply measurableSet_Ici, Measure.restrict_apply measurableSet_Ici,
        hrestrict] at h
    rw [← compl_compl (Ioi c), measure_compl measurableSet_Ioi.compl (measure_ne_top μ _),
      measure_compl measurableSet_Ioi.compl (by rw [hν, ← hclosed]; exact measure_ne_top μ _),
      huniv, hμ, hν, hclosed]

/-- The squared logarithm is integrable up to the endpoint of the angular interval. -/
theorem intervalIntegrable_log_sq :
    IntervalIntegrable (fun t : ℝ ↦ (Real.log t) ^ 2) volume 0 2 :=
  D5.S3.Arith.Robin.ForwardKernel.CommonBandSharpness.intervalIntegrable_log_sq 0 2

/-- Coincident directions have zero product measure. -/
theorem sphere_diag_null :
    (sphereMeasure.prod sphereMeasure) {p | sphereDot p.1 p.2 = 1} = 0 := by
  have hset : MeasurableSet {p : Sphere4D × Sphere4D | sphereDot p.1 p.2 = 1} :=
    continuous_sphereDot_prod.measurable (measurableSet_singleton (1 : ℝ))
  rw [Measure.prod_apply hset]
  have hfiber (n : Sphere4D) : sphereMeasure {n' | sphereDot n n' = 1} = 0 := by
    change sphereMeasure (sphereDot n ⁻¹' {(1 : ℝ)}) = 0
    rw [← Measure.map_apply (measurable_sphereDot n) (measurableSet_singleton (1 : ℝ)),
      sphere_dot_pushforward]
    simp
  simp [hfiber]

private theorem integrable_log_sq_one_sub :
    Integrable (fun x : ℝ ↦ (Real.log (1 - x)) ^ 2) (volume.restrict (Icc (-1 : ℝ) 1)) := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp
  have h := (intervalIntegrable_log_sq.comp_sub_left 1).symm
  convert h using 1 <;> norm_num

private theorem sphere_log_sq_fiber_integral (n : Sphere4D) :
    (∫ n', (Real.log (1 - sphereDot n n')) ^ 2 ∂sphereMeasure) =
      2 * Real.pi * (∫ t : ℝ in (0 : ℝ)..2, (Real.log t) ^ 2) := by
  let g : ℝ → ℝ := fun x ↦ (Real.log (1 - x)) ^ 2
  have hg : Measurable g := by fun_prop
  change (∫ n', g (sphereDot n n') ∂sphereMeasure) = _
  rw [← integral_map (measurable_sphereDot n).aemeasurable hg.aestronglyMeasurable,
    sphere_dot_pushforward, integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]
  congr 1
  rw [← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ))),
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  convert
    (intervalIntegral.integral_comp_sub_left (fun t : ℝ ↦ (Real.log t) ^ 2)
      (a := -1) (b := 1) 1) using 1
  norm_num [g]

/-- The angular logarithmic singularity has integrable square on the product sphere. -/
theorem sphere_log_sq_integrable :
    Integrable (fun p : Sphere4D × Sphere4D ↦ (Real.log (1 - sphereDot p.1 p.2)) ^ 2)
      (sphereMeasure.prod sphereMeasure) := by
  have hdot := continuous_sphereDot_prod.measurable
  have hm : Measurable (fun p : Sphere4D × Sphere4D ↦
      (Real.log (1 - sphereDot p.1 p.2)) ^ 2) := by fun_prop
  refine (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · exact Filter.Eventually.of_forall fun n ↦ by
      have h := integrable_log_sq_one_sub.smul_measure (c := ENNReal.ofReal (2 * Real.pi))
        ENNReal.ofReal_ne_top
      rw [← sphere_dot_pushforward n] at h
      exact h.comp_measurable (measurable_sphereDot n)
  · simp_rw [Real.norm_of_nonneg (sq_nonneg (Real.log (1 - sphereDot _ _))),
      sphere_log_sq_fiber_integral]
    exact integrable_const _

/-- The exact angular integral reduces to one interval integral. -/
theorem sphere_log_sq_integral :
    (∫ p : Sphere4D × Sphere4D, (Real.log (1 - sphereDot p.1 p.2)) ^ 2
        ∂(sphereMeasure.prod sphereMeasure)) =
      8 * Real.pi ^ 2 * (∫ t : ℝ in (0 : ℝ)..2, (Real.log t) ^ 2) := by
  rw [integral_prod _ sphere_log_sq_integrable]
  simp_rw [sphere_log_sq_fiber_integral, integral_const, Measure.real, sphere_measure_univ,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.pi), smul_eq_mul]
  ring

end NullConeGravity
