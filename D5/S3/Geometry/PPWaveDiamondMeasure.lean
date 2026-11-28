/- GID: D5/S3/Geometry/PPWaveDiamondMeasure
   generality: G
   mirror-B: none(waiver:covered-by-perturbed-causal-order-weyl4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Lebesgue volume of the chronological interval between axial endpoints of a quadratic plane wave. -/

import OmegaBuild.Commands
import D5.S3.Geometry.PPWaveChronology
import D5.S3.Geometry.PPWaveDiamond
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
Omega original.

Lebesgue volume of the chronological interval between axial endpoints of a quadratic plane wave.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Omega.PPWaveDiamond

open Real Set MeasureTheory
open scoped ENNReal

private def quadratic (a b : ℝ) (p : ℝ × ℝ) : ℝ := (a * p.1 ^ 2 + b * p.2 ^ 2) / 2

private theorem volume_ellipse {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    volume {p | quadratic a b p < r} = ENNReal.ofReal (π * (2 * r) / sqrt (a * b)) := by
  let fx : ℝ → ℝ := fun x => sqrt a * x
  let fy : ℝ → ℝ := fun y => sqrt b * y
  let S := Metric.ball (0 : ℂ) (sqrt (2 * r))
  let e := Complex.measurableEquivRealProd.symm
  let φ : ℝ × ℝ → ℝ × ℝ := Prod.map fx fy
  have hφ : Measurable φ := by
    dsimp [φ, fx, fy, Prod.map]
    fun_prop
  have hS : MeasurableSet (e ⁻¹' S) := e.measurable measurableSet_ball
  have hpre : φ ⁻¹' (e ⁻¹' S) = {p | quadratic a b p < r} := by
    ext p
    have hsqrt : 0 < sqrt (2 * r) := sqrt_pos.mpr (by positivity)
    change (e (φ p) ∈ S) ↔ quadratic a b p < r
    rw [Metric.mem_ball, dist_zero_right, ← sq_lt_sq₀ (norm_nonneg _) hsqrt.le,
      Complex.sq_norm, sq_sqrt (by positivity)]
    change (sqrt a * p.1) * (sqrt a * p.1) + (sqrt b * p.2) * (sqrt b * p.2) < 2 * r ↔ _
    rw [← sq, ← sq, mul_pow, mul_pow, sq_sqrt ha.le, sq_sqrt hb.le]
    unfold quadratic
    constructor <;> intro h <;> linarith
  have hmap : Measure.map φ volume =
      (ENNReal.ofReal (sqrt a)⁻¹ * ENNReal.ofReal (sqrt b)⁻¹) • volume := by
    change Measure.map (Prod.map fx fy) ((volume : Measure ℝ).prod (volume : Measure ℝ)) = _
    rw [← Measure.map_prod_map volume volume (by dsimp [fx]; fun_prop) (by dsimp [fy]; fun_prop)]
    dsimp only [fx, fy]
    rw [map_volume_mul_left (sqrt_pos.mpr ha).ne', map_volume_mul_left (sqrt_pos.mpr hb).ne',
      abs_of_pos (inv_pos.mpr (sqrt_pos.mpr ha)), abs_of_pos (inv_pos.mpr (sqrt_pos.mpr hb)),
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
    rfl
  have hSm : MeasurableSet S := measurableSet_ball
  have he : volume (e ⁻¹' S) = volume S :=
    Complex.volume_preserving_equiv_real_prod.symm.measure_preimage hSm.nullMeasurableSet
  rw [← hpre, ← Measure.map_apply hφ hS, hmap, Measure.smul_apply, smul_eq_mul]
  change _ * volume (e ⁻¹' S) = _
  rw [he, Complex.volume_ball, ← ENNReal.ofReal_pow (sqrt_nonneg _) 2,
    sq_sqrt (by positivity), ← NNReal.coe_real_pi, ← ENNReal.ofReal_coe_nnreal]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (sqrt_nonneg _)),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), sqrt_mul ha.le]
  congr 1
  field_simp

/-- Volume between two graphs whose difference is a positive elliptic cap. -/
private theorem volume_between_quadratic_graphs
    {a b V : ℝ} (ha : 0 < a) (hb : 0 < b) (hV : 0 < V)
    {lo hi : (ℝ × ℝ) → ℝ} (hlo : Measurable lo) (hhi : Measurable hi)
    (hgap : ∀ p, hi p - lo p = V - quadratic a b p) :
    volume {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (lo (p.1, p.2.1)) (hi (p.1, p.2.1))} =
      ENNReal.ofReal (π * V ^ 2 / sqrt (a * b)) := by
  let S : Set ((ℝ × ℝ) × ℝ) := {p | p.2 ∈ Ioo (lo p.1) (hi p.1)}
  have hS : MeasurableSet S :=
    (measurableSet_lt (hlo.comp measurable_fst) measurable_snd).inter
      (measurableSet_lt measurable_snd (hhi.comp measurable_fst))
  let e : ((ℝ × ℝ) × ℝ) ≃ᵐ ℝ × ℝ × ℝ := MeasurableEquiv.prodAssoc
  have he : {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (lo (p.1, p.2.1)) (hi (p.1, p.2.1))} =
      e.symm ⁻¹' S := by
    rfl
  rw [he, (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ)).symm.measure_preimage
    hS.nullMeasurableSet]
  change ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)) S = _
  rw [Measure.prod_apply hS]
  let height : ℝ × ℝ → ℝ := fun p => max 0 (V - quadratic a b p)
  have hheight : Measurable height := by
    dsimp [height, quadratic]
    fun_prop
  calc
    _ = ∫⁻ p, ENNReal.ofReal (height p) := by
      apply lintegral_congr
      intro p
      change volume (Ioo (lo p) (hi p)) = _
      rw [Real.volume_Ioo, hgap, show height p = max 0 (V - quadratic a b p) by rfl]
      simp
    _ = ∫⁻ t in Ioi 0, volume {p | t < height p} :=
      lintegral_eq_lintegral_meas_lt volume (.of_forall fun _ => le_max_left _ _)
        hheight.aemeasurable
    _ = ∫⁻ t in Ioo 0 V, ENNReal.ofReal (π * (2 * (V - t)) / sqrt (a * b)) := by
      rw [← lintegral_indicator (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))),
        ← lintegral_indicator (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) V))]
      apply lintegral_congr
      intro t
      by_cases ht : 0 < t
      · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht)]
        by_cases htV : t < V
        · rw [indicator_of_mem (show t ∈ Ioo 0 V from ⟨ht, htV⟩)]
          have heq : {p | t < height p} = {p | quadratic a b p < V - t} := by
            ext p
            change t < max 0 (V - quadratic a b p) ↔ _
            rw [lt_max_iff]
            constructor
            · rintro (h | h)
              · exact (not_lt_of_ge ht.le h).elim
              · change quadratic a b p < V - t
                linarith
            · intro h
              right
              change quadratic a b p < V - t at h
              linarith
          rw [heq, volume_ellipse ha hb (sub_pos.mpr htV)]
        · have heq : {p | t < height p} = ∅ := by
            apply eq_empty_iff_forall_notMem.mpr
            intro p hp
            change t < max 0 (V - quadratic a b p) at hp
            have hq : 0 ≤ quadratic a b p := by unfold quadratic; positivity
            exact not_lt_of_ge (max_le ht.le (by linarith only [hq, le_of_not_gt htV])) hp
          rw [heq, measure_empty, indicator_of_notMem (show t ∉ Ioo 0 V from fun h => htV h.2)]
      · rw [indicator_of_notMem (show t ∉ Ioi 0 from ht),
          indicator_of_notMem (show t ∉ Ioo 0 V from fun h => ht h.1)]
    _ = _ := by
      let f : ℝ → ℝ := fun t => π * (2 * (V - t)) / sqrt (a * b)
      have hf : Continuous f := by dsimp [f]; fun_prop
      have hfi : Integrable f (volume.restrict (Ioo 0 V)) :=
        hf.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
      have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 V)] f := by
        filter_upwards [ae_restrict_mem (measurableSet_Ioo : MeasurableSet (Ioo (0 : ℝ) V))]
          with t ht
        have := sub_pos.mpr ht.2
        dsimp [f]
        positivity
      rw [← ofReal_integral_eq_lintegral_ofReal hfi hnn, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hV.le]
      congr 1
      have hF t : HasDerivAt (fun z => π * (2 * V * z - z ^ 2) / sqrt (a * b)) (f t) t := by
        have h := (((hasDerivAt_id t).const_mul (2 * V)).sub
          ((hasDerivAt_id t).pow 2)).const_mul π
        convert h.div_const (sqrt (a * b)) using 1
        · ext z
          simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
        · dsimp [f]
          ring
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hF t)
        (hf.intervalIntegrable 0 V)]
      ring

private def stiffnessX (ω T u : ℝ) : ℝ :=
  ω * (cosh (ω * u) / sinh (ω * u) + cosh (ω * (T - u)) / sinh (ω * (T - u)))

private def stiffnessY (ω T u : ℝ) : ℝ :=
  ω * (cos (ω * u) / sin (ω * u) + cos (ω * (T - u)) / sin (ω * (T - u)))

private theorem stiffness_and_slice {ω T u : ℝ} (hω : 0 < ω)
    (hu : u ∈ Ioo 0 T) (hπ : ω * T < π) :
    0 < stiffnessX ω T u ∧ 0 < stiffnessY ω T u ∧
      1 / sqrt (stiffnessX ω T u * stiffnessY ω T u) = axialSlice ω T u := by
  let a := ω * u
  let b := ω * (T - u)
  have ha : 0 < a := mul_pos hω hu.1
  have hb : 0 < b := mul_pos hω (sub_pos.mpr hu.2)
  have hab : a + b = ω * T := by dsimp [a, b]; ring
  have habπ : a + b < π := hab ▸ hπ
  have hsa := sin_pos_of_pos_of_lt_pi ha (by linarith)
  have hsb := sin_pos_of_pos_of_lt_pi hb (by linarith)
  have hsab := sin_pos_of_pos_of_lt_pi (add_pos ha hb) habπ
  have hha := sinh_pos_iff.mpr ha
  have hhb := sinh_pos_iff.mpr hb
  have hhab := sinh_pos_iff.mpr (add_pos ha hb)
  have hx : stiffnessX ω T u = ω * sinh (a + b) / (sinh a * sinh b) := by
    change ω * (cosh a / sinh a + cosh b / sinh b) = _
    rw [sinh_add]
    field_simp
    ring
  have hy : stiffnessY ω T u = ω * sin (a + b) / (sin a * sin b) := by
    change ω * (cos a / sin a + cos b / sin b) = _
    rw [sin_add]
    field_simp
    ring
  refine ⟨by rw [hx]; positivity, by rw [hy]; positivity, ?_⟩
  change 1 / sqrt (stiffnessX ω T u * stiffnessY ω T u) =
    sqrt (sin a * sinh a * (sin b * sinh b) / (sin (ω * T) * sinh (ω * T))) / ω
  rw [hx, hy, ← hab]
  have he : ω * sinh (a + b) / (sinh a * sinh b) *
      (ω * sin (a + b) / (sin a * sin b)) =
      ω ^ 2 / (sin a * sinh a * (sin b * sinh b) / (sin (a + b) * sinh (a + b))) := by
    field_simp
  rw [he, sqrt_div (sq_nonneg _), sqrt_sq hω.le]
  field_simp

private theorem volume_of_slices {T : ℝ} (hT : 0 < T)
    {S : Set (ℝ × ℝ × ℝ × ℝ)} (hS : MeasurableSet S)
    {f : ℝ → ℝ} (hf : Continuous f) (hn : ∀ u ∈ Ioo 0 T, 0 ≤ f u)
    (hslice : ∀ u ∈ Ioo 0 T, volume (Prod.mk u ⁻¹' S) = ENNReal.ofReal (f u))
    (hempty : ∀ u ∉ Ioo 0 T, Prod.mk u ⁻¹' S = ∅) :
    volume S = ENNReal.ofReal (∫ u in 0..T, f u) := by
  change ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ × ℝ))) _ = _
  rw [Measure.prod_apply hS]
  calc
    _ = ∫⁻ u in Ioo 0 T, ENNReal.ofReal (f u) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro u
      by_cases hu : u ∈ Ioo 0 T
      · rw [indicator_of_mem hu, hslice u hu]
      · rw [indicator_of_notMem hu, hempty u hu, measure_empty]
    _ = _ := by
      have hfi : Integrable f (volume.restrict (Ioo 0 T)) :=
        hf.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
      have hnn : 0 ≤ᵐ[volume.restrict (Ioo 0 T)] f :=
        (ae_restrict_mem measurableSet_Ioo).mono hn
      rw [← ofReal_integral_eq_lintegral_ofReal hfi hnn, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le hT.le]

private theorem measurableSet_longitudinalGraphs {T : ℝ} {lo hi : (ℝ × ℝ × ℝ) → ℝ}
    (hl : Measurable lo) (hh : Measurable hi) :
    MeasurableSet {p : ℝ × ℝ × ℝ × ℝ |
      p.1 ∈ Ioo 0 T ∧ p.2.2.2 ∈ Ioo (lo (p.1, p.2.1, p.2.2.1)) (hi (p.1, p.2.1, p.2.2.1))} :=
  (measurable_fst measurableSet_Ioo).inter
    ((measurableSet_lt (hl.comp (by fun_prop)) (by fun_prop)).inter
      (measurableSet_lt (by fun_prop) (hh.comp (by fun_prop))))

/-- Lebesgue four-volume of the chronological diamond between the two axial endpoints. -/
theorem volume_axialDiamond {ω T V : ℝ}
    (hω : 0 < ω) (hT : 0 < T) (hπ : ω * T < π) (hV : 0 < V) :
    volume (axialDiamond ω T V) = ENNReal.ofReal (exactAxialVolume ω T V) := by
  have hset : axialDiamond ω T V =
      {p | p.1 ∈ Ioo 0 T ∧ p.2.2.2 ∈ Ioo (axisHeight ω p.1 p.2.1 p.2.2.1)
        (V - axisHeight ω (T - p.1) p.2.1 p.2.2.1)} := by
    ext ⟨u, x, y, v⟩
    exact mem_axialDiamond_iff hω hπ
  have hmeas : MeasurableSet (axialDiamond ω T V) := hset ▸
    measurableSet_longitudinalGraphs
      (lo := fun p => axisHeight ω p.1 p.2.1 p.2.2)
      (hi := fun p => V - axisHeight ω (T - p.1) p.2.1 p.2.2)
      (by unfold axisHeight; fun_prop) (by unfold axisHeight; fun_prop)
  let f : ℝ → ℝ := fun u => π * V ^ 2 * axialSlice ω T u
  have hf : Continuous f := by
    change Continuous (fun u => π * V ^ 2 *
      (sqrt (sin (ω * u) * sinh (ω * u) * (sin (ω * (T - u)) * sinh (ω * (T - u))) /
        (sin (ω * T) * sinh (ω * T))) / ω))
    fun_prop
  have hnn u (_ : u ∈ Ioo 0 T) : 0 ≤ f u := by unfold f axialSlice; positivity
  have hslice u (hu : u ∈ Ioo 0 T) :
      volume (Prod.mk u ⁻¹' axialDiamond ω T V) = ENNReal.ofReal (f u) := by
    have hs := stiffness_and_slice hω hu hπ
    have hfiber : Prod.mk u ⁻¹' axialDiamond ω T V =
        {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (axisHeight ω u p.1 p.2.1)
          (V - axisHeight ω (T - u) p.1 p.2.1)} := by
      ext ⟨x, y, v⟩
      simpa only [mem_preimage, mem_ofPred_eq, hu, true_and] using
        (mem_axialDiamond_iff (u := u) (x := x) (y := y) (v := v) (V := V) hω hπ)
    rw [hfiber, volume_between_quadratic_graphs hs.1 hs.2.1 hV
      (lo := fun p => axisHeight ω u p.1 p.2)
      (hi := fun p => V - axisHeight ω (T - u) p.1 p.2)
      (by unfold axisHeight; fun_prop) (by unfold axisHeight; fun_prop) (by
        intro p
        unfold axisHeight stiffnessX stiffnessY quadratic
        ring)]
    congr 1
    dsimp [f]
    rw [← hs.2.2]
    ring
  have he u (hu : u ∉ Ioo 0 T) : Prod.mk u ⁻¹' axialDiamond ω T V = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro ⟨x, y, v⟩ h
    exact hu ((mem_axialDiamond_iff hω hπ).1 h).1
  rw [volume_of_slices hT hmeas hf hnn hslice he, exactAxialVolume]
  congr 1
  exact intervalIntegral.integral_const_mul _ _

/-- Lebesgue four-volume of the Minkowski chronological diamond between the same tips. -/
theorem volume_axialDiamond_flat {T V : ℝ} (hT : 0 < T) (hV : 0 < V) :
    volume (axialDiamond 0 T V) = ENNReal.ofReal (π * V ^ 2 * T ^ 2 / 6) := by
  have hset : axialDiamond 0 T V =
      {p | p.1 ∈ Ioo 0 T ∧ p.2.2.2 ∈ Ioo (flatAxisHeight p.1 p.2.1 p.2.2.1)
        (V - flatAxisHeight (T - p.1) p.2.1 p.2.2.1)} := by
    ext ⟨u, x, y, v⟩
    exact mem_axialDiamond_flat_iff
  have hmeas : MeasurableSet (axialDiamond 0 T V) := hset ▸
    measurableSet_longitudinalGraphs
      (lo := fun p => flatAxisHeight p.1 p.2.1 p.2.2)
      (hi := fun p => V - flatAxisHeight (T - p.1) p.2.1 p.2.2)
      (by unfold flatAxisHeight; fun_prop) (by unfold flatAxisHeight; fun_prop)
  let f : ℝ → ℝ := fun u => π * V ^ 2 * (u * (T - u) / T)
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hnn u (hu : u ∈ Ioo 0 T) : 0 ≤ f u := by
    have h₁ := hu.1
    have h₂ := sub_pos.mpr hu.2
    dsimp [f]
    positivity
  have hslice u (hu : u ∈ Ioo 0 T) :
      volume (Prod.mk u ⁻¹' axialDiamond 0 T V) = ENNReal.ofReal (f u) := by
    let s := 1 / u + 1 / (T - u)
    have hδ := sub_pos.mpr hu.2
    have hs : 0 < s := add_pos (one_div_pos.mpr hu.1) (one_div_pos.mpr hδ)
    have hfiber : Prod.mk u ⁻¹' axialDiamond 0 T V =
        {p : ℝ × ℝ × ℝ | p.2.2 ∈ Ioo (flatAxisHeight u p.1 p.2.1)
          (V - flatAxisHeight (T - u) p.1 p.2.1)} := by
      ext ⟨x, y, v⟩
      simpa only [mem_preimage, mem_ofPred_eq, hu, true_and] using
        (mem_axialDiamond_flat_iff (u := u) (x := x) (y := y) (v := v) (V := V) (T := T))
    rw [hfiber, volume_between_quadratic_graphs hs hs hV
      (lo := fun p => flatAxisHeight u p.1 p.2)
      (hi := fun p => V - flatAxisHeight (T - u) p.1 p.2)
      (by unfold flatAxisHeight; fun_prop) (by unfold flatAxisHeight; fun_prop) (by
        intro p
        unfold flatAxisHeight quadratic s
        field_simp [hu.1.ne', hδ.ne']
        ring)]
    congr 1
    rw [← sq, sqrt_sq hs.le]
    dsimp [f, s]
    field_simp [hu.1.ne', hδ.ne', hT.ne']
    ring
  have he u (hu : u ∉ Ioo 0 T) : Prod.mk u ⁻¹' axialDiamond 0 T V = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro ⟨x, y, v⟩ h
    exact hu (mem_axialDiamond_flat_iff.1 h).1
  rw [volume_of_slices hT hmeas hf hnn hslice he]
  congr 1
  change (∫ u in 0..T, π * V ^ 2 * (u * (T - u) / T)) = _
  rw [intervalIntegral.integral_const_mul, integral_flatSlice hT]
  ring

/-- The chronological diamond has strictly greater four-volume than its flat counterpart. -/
theorem volume_axialDiamond_strict_excess {ω T V : ℝ}
    (hω : 0 < ω) (hT : 0 < T) (hπ : ω * T < π) (hV : 0 < V) :
    ENNReal.ofReal (π * V ^ 2 * T ^ 2 / 6) < volume (axialDiamond ω T V) := by
  rw [volume_axialDiamond hω hT hπ hV]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity) |>.mpr
    (axialVolume_strict_excess hω hT hπ hV)

/-- Direct comparison with the chronological diamond of the flat metric. -/
theorem volume_axialDiamond_flat_lt {ω T V : ℝ}
    (hω : 0 < ω) (hT : 0 < T) (hπ : ω * T < π) (hV : 0 < V) :
    volume (axialDiamond 0 T V) < volume (axialDiamond ω T V) := by
  rw [volume_axialDiamond_flat hT hV]
  exact volume_axialDiamond_strict_excess hω hT hπ hV

end Omega.PPWaveDiamond
