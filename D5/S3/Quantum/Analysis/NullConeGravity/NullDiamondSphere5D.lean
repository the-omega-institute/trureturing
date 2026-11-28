/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondSphere5D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Dot-product density and exact angular square integrability on the unit three-sphere. -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import OmegaMath.Analysis.SemicircleIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Round angular measure for the five-dimensional null cone. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal InnerProductSpace Pointwise Interval

namespace NullConeGravity

abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev Sphere5D := sphere (0 : E4) 1

/-- Haar angular measure on the unit sphere in four Euclidean dimensions. -/
def sphere5DMeasure : Measure Sphere5D := (volume : Measure E4).toSphere

instance sphere5DMeasure_isFinite : IsFiniteMeasure sphere5DMeasure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure E4).toSphere))

/-- Euclidean dot product of two unit directions. -/
def sphere5DDot (n n' : Sphere5D) : ℝ := ⟪(n : E4), (n' : E4)⟫_ℝ

private theorem measurable_sphere5DDot (n : Sphere5D) : Measurable (sphere5DDot n) := by
  unfold sphere5DDot
  fun_prop

theorem continuous_sphere5DDot_prod :
    Continuous (fun p : Sphere5D × Sphere5D ↦ sphere5DDot p.1 p.2) := by
  unfold sphere5DDot
  fun_prop

theorem sphere5D_measure_univ :
    sphere5DMeasure univ = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  rw [sphere5DMeasure, Measure.toSphere_apply_univ,
    InnerProductSpace.volume_ball_of_dim_even (k := 2) (by simp)]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.mul_one]
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1
  ring

private theorem norm_direction (n : Sphere5D) : ‖(n : E4)‖ = 1 := by
  simp

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev HeightSpace := WithLp 2 (ℝ × E3)

private theorem norm_height_sq (z : ℝ) (y : E3) :
    ‖WithLp.toLp 2 (z, y)‖ ^ 2 = z ^ 2 + ‖y‖ ^ 2 := by
  simp [WithLp.prod_norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]

private def heightIsometry (n : Sphere5D) : E4 ≃ₗᵢ[ℝ] HeightSpace := by
  have hdim : Module.finrank ℝ HeightSpace = 4 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × E3)).finrank_eq, Module.finrank_prod]
    simp
  let e : E4 ≃ₗᵢ[ℝ] HeightSpace :=
    ((stdOrthonormalBasis ℝ HeightSpace).reindex (finCongr hdim)).repr.symm
  let pole : E4 := e.symm (WithLp.toLp 2 ((1 : ℝ), (0 : E3)))
  exact ((ℝ ∙ ((n : E4) - pole))ᗮ.reflection).trans e

private theorem heightIsometry_pole (n : Sphere5D) :
    heightIsometry n n = WithLp.toLp 2 ((1 : ℝ), (0 : E3)) := by
  unfold heightIsometry
  rw [LinearIsometryEquiv.trans_apply, Submodule.reflection_sub]
  · simp
  · rw [norm_direction, LinearIsometryEquiv.norm_map,
      ← sq_eq_sq₀ (by norm_num : (0 : ℝ) ≤ 1) (norm_nonneg _), norm_height_sq]
    simp

private theorem heightIsometry_fst (n : Sphere5D) (v : E4) :
    (WithLp.ofLp (heightIsometry n v)).1 = ⟪(n : E4), v⟫_ℝ := by
  rw [← (heightIsometry n).inner_map_map, heightIsometry_pole]
  simp

private def solidCap (c : ℝ) : Set (ℝ × E3) :=
  {p | ‖WithLp.toLp 2 p‖ < 1 ∧ c * ‖WithLp.toLp 2 p‖ < p.1}

private theorem measurableSet_solidCap (c : ℝ) : MeasurableSet (solidCap c) := by
  have hm : Measurable (fun p : ℝ × E3 ↦ ‖WithLp.toLp 2 p‖) :=
    continuous_norm.measurable.comp (MeasurableEquiv.toLp 2 _).measurable
  exact (measurableSet_lt hm measurable_const).inter
    (measurableSet_lt (measurable_const.mul hm) measurable_fst)

private theorem cone_eq_preimage (n : Sphere5D) (c : ℝ) :
    Ioo (0 : ℝ) 1 • (Subtype.val '' (sphere5DDot n ⁻¹' Ioi c)) =
      (WithLp.ofLp ∘ heightIsometry n) ⁻¹' solidCap c := by
  ext v
  change _ ↔ ‖heightIsometry n v‖ < 1 ∧
    c * ‖heightIsometry n v‖ < (WithLp.ofLp (heightIsometry n v)).1
  rw [(heightIsometry n).norm_map, heightIsometry_fst]
  constructor
  · rintro ⟨r, ⟨hr₀, hr₁⟩, _, ⟨w, hw, rfl⟩, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr₀, norm_direction, mul_one,
      real_inner_smul_right]
    exact ⟨hr₁, by simpa [mul_comm, sphere5DDot] using (mul_lt_mul_of_pos_left hw hr₀)⟩
  · rintro ⟨h₁, hc⟩
    have hv : ‖v‖ ≠ 0 := by
      intro h
      simp [norm_eq_zero.mp h] at hc
    let w : Sphere5D := ⟨‖v‖⁻¹ • v, by
      simp [norm_smul, hv]⟩
    refine ⟨‖v‖, ⟨lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv), h₁⟩, w, ⟨w, ?_, rfl⟩, ?_⟩
    · change c < ⟪(n : E4), ‖v‖⁻¹ • v⟫_ℝ
      rw [real_inner_smul_right, ← div_eq_inv_mul]
      exact (lt_div_iff₀ (lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv))).2 hc
    · simp [w, smul_smul, hv]

private theorem volume_slice (q : ℝ) :
    (volume : Measure E3) {y | ‖y‖ ^ 2 < q} =
      ENNReal.ofReal ((Real.pi * 4 / 3) * Real.sqrt q ^ 3) := by
  have hs : {y : E3 | ‖y‖ ^ 2 < q} = ball 0 (Real.sqrt q) := by
    ext y
    simp [mem_ball, dist_zero_right, Real.lt_sqrt (norm_nonneg y)]
  rw [hs, EuclideanSpace.volume_ball_fin_three,
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), mul_comm,
    ← ENNReal.ofReal_mul (by positivity)]

-- Below height c the cone limits the slice radius. Above c the unit ball limits it.
private theorem solidCap_fibres (c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (z : ℝ) :
    (volume : Measure E3) (Prod.mk z ⁻¹' solidCap c) =
      (Ioc 0 c).indicator
        (fun t : ℝ ↦ ENNReal.ofReal ((Real.pi * 4 / 3 * Real.sqrt (1 - c ^ 2) ^ 3 / c ^ 3) *
          t ^ 3)) z +
      (Ioc c 1).indicator (fun t : ℝ ↦
        ENNReal.ofReal ((Real.pi * 4 / 3) * Real.sqrt (1 - t ^ 2) ^ 3)) z := by
  have hnorm : ∀ y : E3, 0 ≤ ‖WithLp.toLp 2 (z, y)‖ := fun _ ↦ norm_nonneg _
  by_cases hlow : z ∈ Ioc 0 c
  · have hz₀ : 0 < z := hlow.1
    have hzc : z ≤ c := hlow.2
    have hc : 0 < c := hz₀.trans_le hzc
    have hc_sq : 0 < c ^ 2 := by positivity
    have hc_sq_le : c ^ 2 ≤ 1 := by nlinarith
    have hupp : z ∉ Ioc c 1 := fun hz ↦ hz.1.not_ge hzc
    rw [indicator_of_mem hlow, indicator_of_notMem hupp, add_zero]
    have hfibre : Prod.mk z ⁻¹' solidCap c = {y : E3 | ‖y‖ ^ 2 < (1 - c ^ 2) / c ^ 2 * z ^ 2} := by
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
    rw [hfibre, volume_slice, Real.sqrt_mul (by positivity),
      Real.sqrt_div (sub_nonneg.mpr hc_sq_le), Real.sqrt_sq hc₀, Real.sqrt_sq hz₀.le]
    congr 1
    ring
  · rw [indicator_of_notMem hlow, zero_add]
    by_cases hupp : z ∈ Ioc c 1
    · have hz₀ : 0 ≤ z := hc₀.trans hupp.1.le
      have hz₁ : z ≤ 1 := hupp.2
      rw [indicator_of_mem hupp]
      have hfibre : Prod.mk z ⁻¹' solidCap c = {y : E3 | ‖y‖ ^ 2 < 1 - z ^ 2} := by
        ext y
        change (‖WithLp.toLp 2 (z, y)‖ < 1 ∧ c * ‖WithLp.toLp 2 (z, y)‖ < z) ↔ _
        have hball : ‖WithLp.toLp 2 (z, y)‖ < 1 ↔ ‖y‖ ^ 2 < 1 - z ^ 2 := by
          rw [← sq_lt_sq₀ (hnorm y) (by norm_num : (0 : ℝ) ≤ 1), norm_height_sq]
          constructor <;> intro h <;> linarith
        exact ⟨fun h ↦ hball.mp h.1, fun h ↦ ⟨hball.mpr h,
          (mul_le_of_le_one_right hc₀ (hball.mpr h).le).trans_lt hupp.1⟩⟩
      rw [hfibre, volume_slice]
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
    (volume : Measure (ℝ × E3)) (solidCap c) =
      ENNReal.ofReal (Real.pi * (∫ t in c..1, Real.sqrt (1 - t ^ 2))) := by
  have hc_sq_le : c ^ 2 ≤ 1 := by nlinarith
  let k : ℝ := Real.pi * 4 / 3
  let g : ℝ → ℝ := fun t ↦ Real.sqrt (1 - t ^ 2)
  let a : ℝ := k * g c ^ 3 / c ^ 3
  have ha : 0 ≤ a := by dsimp [a, k, g]; positivity
  have hg : Continuous g := by dsimp [g]; fun_prop
  have h₁ : IntervalIntegrable (fun t : ℝ ↦ a * t ^ 3) volume 0 c :=
    (show Continuous (fun t : ℝ ↦ a * t ^ 3) by fun_prop).intervalIntegrable ..
  have h₂ : IntervalIntegrable (fun t : ℝ ↦ k * g t ^ 3) volume c 1 :=
    (continuous_const.mul (hg.pow 3)).intervalIntegrable ..
  have hrel := Omega.semicircle_cap_integral hc₀ hc₁
  change (∫ t in c..1, g t) = c * g c ^ 3 / 3 + (4 / 3) * ∫ t in c..1, g t ^ 3 at hrel
  change ((volume : Measure ℝ).prod (volume : Measure E3)) (solidCap c) = _
  rw [Measure.prod_apply (measurableSet_solidCap c)]
  simp_rw [solidCap_fibres c hc₀ hc₁]
  change (∫⁻ t, (Ioc 0 c).indicator (fun t ↦ ENNReal.ofReal (a * t ^ 3)) t +
    (Ioc c 1).indicator (fun t ↦ ENNReal.ofReal (k * g t ^ 3)) t) = _
  rw [lintegral_add_left, lintegral_indicator measurableSet_Ioc,
    lintegral_indicator measurableSet_Ioc]
  · rw [← ofReal_integral_eq_lintegral_ofReal h₁.1,
      ← ofReal_integral_eq_lintegral_ofReal h₂.1,
      ← intervalIntegral.integral_of_le hc₀, ← intervalIntegral.integral_of_le hc₁,
      ← ENNReal.ofReal_add]
    · rw [intervalIntegral.integral_const_mul, integral_pow 3, intervalIntegral.integral_const_mul,
        hrel]
      congr 1
      by_cases hc : c = 0
      · simp [a, k, hc]
        ring
      · dsimp [a, k]
        field_simp
        ring
    · exact intervalIntegral.integral_nonneg hc₀ fun t ht ↦ by
        exact mul_nonneg ha (pow_nonneg ht.1 3)
    · exact intervalIntegral.integral_nonneg hc₁ fun _ _ ↦ by dsimp [k, g]; positivity
    · exact Filter.Eventually.of_forall fun _ ↦ by dsimp [k, g]; positivity
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact mul_nonneg ha (pow_nonneg ht.1.le 3)
  · apply Measurable.indicator _ measurableSet_Ioc
    fun_prop

private theorem sphere_cap_eq_solid (n : Sphere5D) (c : ℝ) :
    Measure.map (sphere5DDot n) sphere5DMeasure (Ioi c) =
      4 * (volume : Measure (ℝ × E3)) (solidCap c) := by
  rw [Measure.map_apply (measurable_sphere5DDot n) measurableSet_Ioi, sphere5DMeasure,
    Measure.toSphere_apply' _ ((measurable_sphere5DDot n) measurableSet_Ioi),
    cone_eq_preimage]
  have hmp : MeasurePreserving (WithLp.ofLp ∘ heightIsometry n) :=
    (WithLp.volume_preserving_ofLp _ _).comp (heightIsometry n).measurePreserving
  rw [hmp.measure_preimage (measurableSet_solidCap c).nullMeasurableSet]
  norm_num

private theorem measure_eq_of_upper_tails {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    (huniv : μ univ = ν univ) (htails : ∀ c : ℝ, μ (Ioi c) = ν (Ioi c)) : μ = ν := by
  refine Measure.ext_of_generateFrom_of_cover
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioi ℝ))
    (countable_singleton univ) isPiSystem_Ioi (by simp)
    (fun t _ ↦ measure_ne_top μ t) ?_ ?_
  · rintro t (rfl : t = univ) _ ⟨c, rfl⟩
    simpa using htails c
  · simpa using huniv

theorem sphere5D_dot_bounds (n n' : Sphere5D) : -1 ≤ sphere5DDot n n' ∧ sphere5DDot n n' ≤ 1 := by
  have h := abs_real_inner_le_norm (n : E4) (n' : E4)
  rw [norm_direction n, norm_direction n', mul_one] at h
  exact abs_le.mp h

private def angularDensity (x : ℝ) : ℝ := 4 * Real.pi * Real.sqrt (1 - x ^ 2)

private def dotTarget : Measure ℝ :=
  (volume.restrict (Icc (-1 : ℝ) 1)).withDensity (fun x ↦ ENNReal.ofReal (angularDensity x))

private theorem continuous_angularDensity : Continuous angularDensity := by
  unfold angularDensity
  fun_prop

private theorem angularDensity_nonneg (x : ℝ) : 0 ≤ angularDensity x := by
  unfold angularDensity
  positivity

private theorem target_apply {s : Set ℝ} (hs : MeasurableSet s) :
    dotTarget s = ∫⁻ x in s ∩ Icc (-1 : ℝ) 1, ENNReal.ofReal (angularDensity x) := by
  rw [dotTarget, withDensity_apply _ hs, Measure.restrict_restrict hs]

private theorem dotTarget_univ : dotTarget univ = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  rw [target_apply MeasurableSet.univ, univ_inter,
    ← ofReal_integral_eq_lintegral_ofReal (continuous_angularDensity.integrableOn_Icc)
      (Filter.Eventually.of_forall angularDensity_nonneg),
    ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ))),
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  unfold angularDensity
  rw [intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq]
  congr 1
  ring

private theorem map_sphere5DDot_univ (n : Sphere5D) :
    (Measure.map (sphere5DDot n) sphere5DMeasure) univ = ENNReal.ofReal (2 * Real.pi ^ 2) := by
  rw [Measure.map_apply (measurable_sphere5DDot n) MeasurableSet.univ, preimage_univ,
    sphere5D_measure_univ]

private theorem dot_upper_tail (n : Sphere5D) (c : ℝ) (hc : 0 ≤ c) :
    Measure.map (sphere5DDot n) sphere5DMeasure (Ioi c) = dotTarget (Ioi c) := by
  by_cases h₁ : c ≤ 1
  · have hset : Ioi c ∩ Icc (-1 : ℝ) 1 = Ioc c 1 := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
      exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, by linarith [h.1], h.2⟩⟩
    rw [sphere_cap_eq_solid, volume_solidCap c hc h₁, target_apply measurableSet_Ioi, hset,
      ← ofReal_integral_eq_lintegral_ofReal (continuous_angularDensity.intervalIntegrable c 1).1
        (Filter.Eventually.of_forall angularDensity_nonneg),
      ← intervalIntegral.integral_of_le h₁]
    unfold angularDensity
    rw [intervalIntegral.integral_const_mul, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  · have hempty : Ioi c ∩ Icc (-1 : ℝ) 1 = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx ↦ h₁ (hx.1.le.trans hx.2.2)
    have hpre : sphere5DDot n ⁻¹' Ioi c = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun w hw ↦
        h₁ ((show c < sphere5DDot n w from hw).le.trans (sphere5D_dot_bounds n w).2)
    rw [Measure.map_apply (measurable_sphere5DDot n) measurableSet_Ioi, hpre,
      target_apply measurableSet_Ioi, hempty, measure_empty, setLIntegral_empty]

private theorem map_neg_dotTarget : dotTarget.map (fun x : ℝ ↦ -x) = dotTarget := by
  ext s hs
  let e := MeasurableEquiv.neg ℝ
  have hpre : e ⁻¹' Icc (-1 : ℝ) 1 = Icc (-1 : ℝ) 1 := by
    ext x
    change (-1 ≤ -x ∧ -x ≤ 1) ↔ (-1 ≤ x ∧ x ≤ 1)
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hmp : MeasurePreserving e volume volume := ⟨measurable_neg, Measure.map_neg_eq_self volume⟩
  rw [Measure.map_apply measurable_neg hs, target_apply (measurable_neg hs), target_apply hs]
  change (∫⁻ x in (e ⁻¹' s) ∩ Icc (-1 : ℝ) 1, _) = _
  rw [← hpre, ← Set.preimage_inter,
    ← hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding]
  simp [e, angularDensity]

private theorem map_neg_sphere5DDot (n : Sphere5D) :
    (Measure.map (sphere5DDot n) sphere5DMeasure).map (fun x : ℝ ↦ -x) =
      Measure.map (sphere5DDot n) sphere5DMeasure := by
  let m : Sphere5D := ⟨-(n : E4), by simp⟩
  have hneg : (fun x : ℝ ↦ -x) ∘ sphere5DDot n = sphere5DDot m := by
    funext w
    simp [sphere5DDot, m]
  rw [Measure.map_map measurable_neg (measurable_sphere5DDot n), hneg]
  have hfinite := sphere5DMeasure.isFiniteMeasure_map (sphere5DDot m)
  exact measure_eq_of_upper_tails (by rw [map_sphere5DDot_univ, map_sphere5DDot_univ])
    (fun c ↦ by rw [sphere_cap_eq_solid, sphere_cap_eq_solid])

/-- The dot product with any fixed unit direction has the same semicircle density. -/
theorem sphere5D_dot_pushforward (n : Sphere5D) :
    Measure.map (sphere5DDot n) sphere5DMeasure = (volume.restrict (Icc (-1 : ℝ) 1)).withDensity
      (fun x ↦ ENNReal.ofReal (4 * Real.pi * Real.sqrt (1 - x ^ 2))) := by
  let μ := Measure.map (sphere5DDot n) sphere5DMeasure
  change μ = dotTarget
  have hfinite : IsFiniteMeasure μ := sphere5DMeasure.isFiniteMeasure_map (sphere5DDot n)
  have huniv : μ univ = dotTarget univ := by rw [dotTarget_univ, map_sphere5DDot_univ]
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
    have hset : (fun x : ℝ ↦ -x) ⁻¹' Ici (-c) = (Ioi c)ᶜ := by ext x; simp
    have hμ : μ ((Ioi c)ᶜ) = μ (Ici (-c)) := by
      rw [← hset, ← Measure.map_apply measurable_neg measurableSet_Ici, map_neg_sphere5DDot]
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

/-- The dot-product distribution is invariant under orthogonal rotation of the pole. -/
theorem sphere5D_dot_rotation (R : E4 ≃ₗᵢ[ℝ] E4) (n : Sphere5D) :
    Measure.map (fun w : Sphere5D ↦ ⟪R (n : E4), (w : E4)⟫_ℝ) sphere5DMeasure =
      Measure.map (sphere5DDot n) sphere5DMeasure := by
  let nR : Sphere5D := ⟨R (n : E4), by simpa using norm_direction n⟩
  exact (sphere5D_dot_pushforward nR).trans (sphere5D_dot_pushforward n).symm

/-- Bochner-integral form of the semicircle law, with the round-sphere normalization. -/
theorem sphere5D_dot_integral (n : Sphere5D) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ w, f (sphere5DDot n w) ∂sphere5DMeasure) =
      4 * Real.pi * ∫ x in (-1 : ℝ)..1, f x * Real.sqrt (1 - x ^ 2) := by
  rw [← integral_map (measurable_sphere5DDot n).aemeasurable hf.aestronglyMeasurable,
    sphere5D_dot_pushforward, integral_withDensity_eq_integral_toReal_smul
      (by fun_prop) (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top),
    ← Measure.restrict_congr_set (Ioc_ae_eq_Icc (μ := (volume : Measure ℝ))),
    ← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by norm_num)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  change (ENNReal.ofReal (angularDensity x)).toReal • f x = _
  rw [ENNReal.toReal_ofReal (angularDensity_nonneg x), smul_eq_mul]
  unfold angularDensity
  ring

/-- The diagonal angular singularity occupies a product null set. -/
theorem sphere5D_diag_null :
    (sphere5DMeasure.prod sphere5DMeasure) {p | sphere5DDot p.1 p.2 = 1} = 0 := by
  have hset : MeasurableSet {p : Sphere5D × Sphere5D | sphere5DDot p.1 p.2 = 1} :=
    continuous_sphere5DDot_prod.measurable (measurableSet_singleton 1)
  rw [Measure.prod_apply hset]
  have hfiber (n : Sphere5D) : sphere5DMeasure {w | sphere5DDot n w = 1} = 0 := by
    change sphere5DMeasure (sphere5DDot n ⁻¹' {1}) = 0
    rw [← Measure.map_apply (measurable_sphere5DDot n) (measurableSet_singleton 1),
      sphere5D_dot_pushforward, withDensity_apply _ (measurableSet_singleton 1),
      Measure.restrict_restrict (measurableSet_singleton 1)]
    rw [Measure.restrict_eq_zero.mpr (measure_mono_null inter_subset_left (by simp))]
    simp
  change (∫⁻ n, sphere5DMeasure {w | sphere5DDot n w = 1} ∂sphere5DMeasure) = 0
  simp_rw [hfiber, lintegral_zero]

private theorem inverse_section (n : Sphere5D) :
    Integrable (fun w ↦ (1 - sphere5DDot n w)⁻¹) sphere5DMeasure ∧
      (∫ w, (1 - sphere5DDot n w)⁻¹ ∂sphere5DMeasure) = 4 * Real.pi ^ 2 := by
  let f : ℝ → ℝ := fun x ↦ (1 - x)⁻¹
  have hf : Measurable f := by dsimp [f]; fun_prop
  have h := Omega.semicircle_div_one_sub
  refine ⟨?_, ?_⟩
  · apply Integrable.comp_measurable (g := f) _ (measurable_sphere5DDot n)
    rw [sphere5D_dot_pushforward, integrable_withDensity_iff
      (by fun_prop) (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    convert h.1.const_mul (4 * Real.pi) using 1
    ext x
    change f x * (ENNReal.ofReal (angularDensity x)).toReal = _
    rw [ENNReal.toReal_ofReal (angularDensity_nonneg x)]
    dsimp [f, angularDensity]
    ring
  · change (∫ w, f (sphere5DDot n w) ∂sphere5DMeasure) = _
    rw [sphere5D_dot_integral n f hf, intervalIntegral.integral_of_le (by norm_num),
      Measure.restrict_congr_set Ioc_ae_eq_Icc]
    have heq (x : ℝ) : f x * Real.sqrt (1 - x ^ 2) = Real.sqrt (1 - x ^ 2) / (1 - x) := by
      exact mul_comm _ _
    simp_rw [heq, h.2]
    ring

/-- The square of the inverse square-root angular singularity is integrable. -/
theorem sphere5D_inv_sqrt_sq_integrable :
    Integrable (fun p : Sphere5D × Sphere5D ↦ (1 - sphere5DDot p.1 p.2)⁻¹)
      (sphere5DMeasure.prod sphere5DMeasure) := by
  have hm : Measurable (fun p : Sphere5D × Sphere5D ↦ (1 - sphere5DDot p.1 p.2)⁻¹) := by
    exact (measurable_const.sub continuous_sphere5DDot_prod.measurable).inv
  refine (integrable_prod_iff hm.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall fun n ↦ (inverse_section n).1, ?_⟩
  simp_rw [Real.norm_of_nonneg (inv_nonneg.mpr (sub_nonneg.mpr (sphere5D_dot_bounds _ _).2)),
    (inverse_section _).2]
  exact integrable_const _

/-- The square of the angular singularity has exact integral eight times π to the fourth. -/
theorem sphere5D_inv_sqrt_sq_integral :
    (∫ p : Sphere5D × Sphere5D, (1 - sphere5DDot p.1 p.2)⁻¹
      ∂(sphere5DMeasure.prod sphere5DMeasure)) = 8 * Real.pi ^ 4 := by
  rw [integral_prod _ sphere5D_inv_sqrt_sq_integrable]
  simp_rw [(inverse_section _).2, integral_const, Measure.real, sphere5D_measure_univ,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Real.pi ^ 2), smul_eq_mul]
  ring

/-- The inverse square-root angular kernel belongs to complex L². -/
theorem sphere5D_inv_sqrt_memLp :
    MemLp (fun p : Sphere5D × Sphere5D ↦
      ((1 / Real.sqrt (1 - sphere5DDot p.1 p.2) : ℝ) : ℂ)) 2
      (sphere5DMeasure.prod sphere5DMeasure) := by
  have hm : Measurable (fun p : Sphere5D × Sphere5D ↦
      ((1 / Real.sqrt (1 - sphere5DDot p.1 p.2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (measurable_const.div (Real.continuous_sqrt.measurable.comp
        (measurable_const.sub continuous_sphere5DDot_prod.measurable)))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).2
  convert sphere5D_inv_sqrt_sq_integrable using 1
  ext p
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, one_pow, Real.sq_sqrt
    (sub_nonneg.mpr (sphere5D_dot_bounds _ _).2), one_div]

end NullConeGravity
