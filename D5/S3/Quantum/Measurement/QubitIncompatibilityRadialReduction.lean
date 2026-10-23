/- GID: D5/S3/Quantum/Measurement/QubitIncompatibilityRadialReduction
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/QubitIncompatibilityRadialReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative cosines reduce incompatible volume to ordered-root coordinates. -/

/-
admission_basis: escape-witness
Direct frozen dependencies: none (the only D5 imports belong to this delivery).
The public content theorem volume_NJM_rootI uses meridian_surjective.
The inverse witness is explicitly constructed; normalization alone leaves its existence open.
Four-slot escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15930
The meridian target uses Mathlib's upperHalfPlaneSet through Complex.equivRealProd.
Declaration rows: name | proof_shape | escape_witness | one direct consumer.
Definitions have no proof term; their bind-only label supplies no admission witness.
domain | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.spherical_lintegral_inner
meridian | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.meridian_surjective
cosine_square_lt_one | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.det_meridianDerivative
meridian_norm_square | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.meridian_surjective
meridian_injective | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.meridian_change_lintegral
meridian_mapsTo | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.meridian_surjective
meridian_surjective | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.meridian_image
meridian_image | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.meridian_change_lintegral
meridianDerivative | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.det_meridianDerivative
hasFDerivAt_meridian | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.meridian_change_lintegral
det_meridianDerivative | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.meridian_change_lintegral
meridian_change_lintegral | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.spherical_lintegral_prod
norm_lintegral | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.norm_lintegral_three
norm_lintegral_two | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.cylindrical_lintegral
norm_lintegral_three | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.relative_cosine_lintegral
cylindrical_lintegral | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.spherical_lintegral_prod
spherical_lintegral_prod | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.spherical_lintegral_axis
axialSplit | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.axialSplit_norm
axialSplit_measurePreserving | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.spherical_lintegral_axis
axialSplit_fst | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.axialSplit_norm
axialSplit_norm | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.spherical_lintegral_axis
spherical_lintegral_axis | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.spherical_lintegral_inner
axisReflection | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.spherical_lintegral_inner
axisReflection_self | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.axisReflection_inner
axisReflection_inner | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.spherical_lintegral_inner
norm_mul_cosine | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.spherical_lintegral_inner
spherical_lintegral_inner | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.relative_cosine_lintegral
relative_cosine_lintegral | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.volume_positiveSector_radial
interiorPositiveSector | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_eq_interior
measurableSet_interiorPositiveSector | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_radial
null_lift_first | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_eq_interior
null_lift_second | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_eq_interior
volume_positiveSector_eq_interior | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_radial
radialCriterion | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.radialKernel_measurable
radialKernel | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_radialBody
radialKernel_measurable | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.measurable_radialKernel
volume_positiveSector_radial | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.volume_positiveSector_radial_regroup
measurable_radialKernel | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_radial_regroup
angular_domain_split | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_radial_regroup
volume_positiveSector_radial_regroup | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.volume_positiveSector_radialBody
scalarCriterion | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.angularIntegral_measurable
angularIntegral | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.weightedAngular
angularIntegral_measurable | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.weightedAngular_measurable
angularIntegral_eq_volume | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.angularIntegral_coordinates
radialKernel_body_indicator | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.weighted_kernel_body
measurableSet_radialBody | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.radialBody_fubini
weightedAngular | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_ordered
weightedAngular_measurable | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_radialBody
weighted_kernel_body | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_radialBody
radialBody_fubini | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_positiveSector_radialBody
volume_positiveSector_radialBody | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.volume_positiveSector_ordered
coordinateJacobian | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.coordinateJacobian_pos
volume_positiveSector_ordered | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityRadialReduction.volume_NJM_rootI
angularIntegral_coordinates | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.coordinate_weight_cancellation
rootDensity | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.root_square_cancellation
rootI | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityProbability.rootI_eq_squareI
coordinateJacobian_pos | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.coordinate_weight_cancellation
coordinate_weight_cancellation | proof_shape: bind-only | escape_witness: none | QubitIncompatibilityRadialReduction.volume_NJM_rootI
volume_NJM_rootI | proof_shape: content | escape_witness: meridian_surjective | QubitIncompatibilityProbability.volume_NJM_cubeI
-/

import D5.S3.Quantum.Measurement.OrderedRootCoordinates
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace
noncomputable section
open D5.S3.Quantum.Measurement.OrderedRootCoordinates
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction

private def domain : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioo (-1 : ℝ) 1

private def meridian (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1 * p.2, p.1 * Real.sqrt (1 - p.2 ^ 2))

private theorem cosine_square_lt_one {s : ℝ} (hs : s ∈ Ioo (-1 : ℝ) 1) : s ^ 2 < 1 := by
  nlinarith [hs.1, hs.2]

private theorem meridian_norm_square {p : ℝ × ℝ} (hp : p ∈ domain) :
    (meridian p).1 ^ 2 + (meridian p).2 ^ 2 = p.1 ^ 2 := by
  have hsq := Real.sq_sqrt (show 0 ≤ 1 - p.2 ^ 2 by
    linarith [cosine_square_lt_one hp.2])
  simp only [meridian, mul_pow]
  rw [hsq]
  ring

private theorem meridian_injective : InjOn meridian domain := by
  intro p hp q hq he
  have hpn := meridian_norm_square hp
  have hqn := meridian_norm_square hq
  rw [he] at hpn
  have hpr : 0 < p.1 := hp.1
  have hqr : 0 < q.1 := hq.1
  have hrad : p.1 = q.1 := by nlinarith only [hpn, hqn, hpr, hqr]
  have hfst : p.1 * p.2 = q.1 * q.2 := congrArg Prod.fst he
  apply Prod.ext hrad
  rw [← hrad] at hfst
  exact (mul_left_cancel₀ (ne_of_gt hp.1)) hfst

private theorem meridian_mapsTo : MapsTo meridian domain (Complex.equivRealProd.symm ⁻¹' UpperHalfPlane.upperHalfPlaneSet) := by
  intro p hp
  change 0 < p.1 * Real.sqrt (1 - p.2 ^ 2)
  exact mul_pos hp.1 (Real.sqrt_pos.mpr (by linarith [cosine_square_lt_one hp.2]))

private theorem meridian_surjective : (Complex.equivRealProd.symm ⁻¹' UpperHalfPlane.upperHalfPlaneSet) ⊆ meridian '' domain := by
  intro p hp
  have hy : 0 < p.2 := hp
  let r := Real.sqrt (p.1 ^ 2 + p.2 ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_pos hy, sq_nonneg p.1])
  have hr2 : r ^ 2 = p.1 ^ 2 + p.2 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hs : p.1 / r ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · rw [lt_div_iff₀ hr]
      nlinarith only [hr, hr2, sq_pos_of_pos hy]
    · rw [div_lt_iff₀ hr]
      nlinarith only [hr, hr2, sq_pos_of_pos hy]
  refine ⟨(r, p.1 / r), ⟨hr, hs⟩, ?_⟩
  apply Prod.ext
  · change r * (p.1 / r) = p.1
    field_simp
  · have hnorm := meridian_norm_square (show (r, p.1 / r) ∈ domain from ⟨hr, hs⟩)
    have hpos := meridian_mapsTo (show (r, p.1 / r) ∈ domain from ⟨hr, hs⟩)
    have hfst : (meridian (r, p.1 / r)).1 = p.1 := by
      dsimp [meridian]; field_simp
    rw [hfst] at hnorm
    have hpos' : 0 < (meridian (r, p.1 / r)).2 := hpos
    nlinarith only [hnorm, hpos', hr2, hy]

private theorem meridian_image : meridian '' domain = (Complex.equivRealProd.symm ⁻¹' UpperHalfPlane.upperHalfPlaneSet) :=
  Subset.antisymm (by rintro q ⟨p, hp, rfl⟩; exact meridian_mapsTo hp) meridian_surjective

private def meridianDerivative (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![p.2, p.1; Real.sqrt (1 - p.2 ^ 2), -p.1 * p.2 / Real.sqrt (1 - p.2 ^ 2)]).toContinuousLinearMap

private theorem hasFDerivAt_meridian {p : ℝ × ℝ} (hp : p ∈ domain) :
    HasFDerivAt meridian (meridianDerivative p) p := by
  have harg : 0 < 1 - p.2 ^ 2 := by linarith [cosine_square_lt_one hp.2]
  have hroot : Real.sqrt (1 - p.2 ^ 2) ≠ 0 := (Real.sqrt_pos.mpr harg).ne'
  have hh := (((hasFDerivAt_snd (𝕜 := ℝ) (p := p)).pow 2).const_sub 1).sqrt harg.ne'
  unfold meridianDerivative
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert! ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul hasFDerivAt_snd).prodMk
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul hh) using 1
  all_goals first | rfl | (ext q <;> simp [ContinuousLinearMap.prod_apply,
    smul_smul, smul_eq_mul, add_comm, div_eq_mul_inv] <;> field_simp <;> ring)

private theorem det_meridianDerivative {p : ℝ × ℝ} (hp : p ∈ domain) :
    (meridianDerivative p).det = -p.1 / Real.sqrt (1 - p.2 ^ 2) := by
  have harg : 0 < 1 - p.2 ^ 2 := by linarith [cosine_square_lt_one hp.2]
  have hroot : Real.sqrt (1 - p.2 ^ 2) ≠ 0 := (Real.sqrt_pos.mpr harg).ne'
  have hs := Real.sq_sqrt harg.le
  unfold meridianDerivative
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  field_simp
  linear_combination -p.1 * hs

private theorem meridian_change_lintegral (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in (Complex.equivRealProd.symm ⁻¹' UpperHalfPlane.upperHalfPlaneSet), ENNReal.ofReal p.2 * f p) =
      ∫⁻ p in domain, ENNReal.ofReal (p.1 ^ 2) * f (meridian p) := by
  have hd : ∀ p ∈ domain, HasFDerivWithinAt meridian (meridianDerivative p) domain p :=
    fun p hp => (hasFDerivAt_meridian hp).hasFDerivWithinAt
  have hm : MeasurableSet domain := measurableSet_Ioi.prod measurableSet_Ioo
  rw [← meridian_image,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hm hd meridian_injective]
  apply setLIntegral_congr_fun hm
  intro p hp
  dsimp only
  rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [det_meridianDerivative hp, abs_div, abs_neg,
    abs_of_pos hp.1, abs_of_pos (Real.sqrt_pos.mpr (by linarith [cosine_square_lt_one hp.2]))]
  simp only [meridian]
  have hroot : Real.sqrt (1 - p.2 ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith [cosine_square_lt_one hp.2])).ne'
  congr 1
  field_simp

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open Set MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction

private theorem norm_lintegral (n : ℕ) [NeZero n] (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : EuclideanSpace ℝ (Fin n), f ‖x‖) =
      (n : ℝ≥0∞) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) *
        ∫⁻ r : ℝ in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ : Measure E := volume
  have hdim : Module.finrank ℝ E = n := by simp [E]
  calc
    (∫⁻ x : E, f ‖x‖ ∂μ) =
        ∫⁻ x : ({(0 : E)}ᶜ : Set E), f ‖x.1‖ ∂μ.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl (fun x : E => f ‖x‖),
        restrict_compl_singleton]
    _ = ∫⁻ p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ), f p.2
        ∂μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1)) := by
      simpa only [homeomorphUnitSphereProd_apply_snd_coe] using
        μ.measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
          (Homeomorph.measurableEmbedding _) (fun p => f p.2)
    _ = μ.toSphere univ * ∫⁻ r : Ioi (0 : ℝ), f r
        ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1) := by
      rw [lintegral_prod (fun p : Metric.sphere (0 : E) 1 × Ioi (0 : ℝ) => f p.2)
        ((hf.comp measurable_subtype_coe).comp measurable_snd).aemeasurable]
      simp [mul_comm]
    _ = (n : ℝ≥0∞) * μ (Metric.ball 0 1) *
        ∫⁻ r : ℝ in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r := by
      rw [Measure.toSphere_apply_univ, hdim]
      congr 1
      rw [Measure.volumeIoiPow, lintegral_withDensity_eq_lintegral_mul]
      · simpa only [Pi.mul_apply] using (lintegral_subtype_comap measurableSet_Ioi
          (fun r : ℝ => ENNReal.ofReal (r ^ (n - 1)) * f r))
      · measurability
      · exact hf.comp measurable_subtype_coe

private theorem norm_lintegral_two (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : EuclideanSpace ℝ (Fin 2), f ‖x‖) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ r : ℝ in Ioi (0 : ℝ), ENNReal.ofReal r * f r := by
  rw [norm_lintegral 2 f hf]
  simp only [EuclideanSpace.volume_ball_fin_two, ENNReal.ofReal_one, one_pow,
    one_mul, Nat.reduceSub, pow_one]
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private theorem norm_lintegral_three (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : EuclideanSpace ℝ (Fin 3), f ‖x‖) =
      ENNReal.ofReal (4 * Real.pi) * ∫⁻ r : ℝ in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) * f r := by
  rw [norm_lintegral 3 f hf]
  simp only [EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow,
    one_mul, Nat.reduceSub]
  have he : (3 : ℝ≥0∞) * ENNReal.ofReal (Real.pi * 4 / 3) =
      ENNReal.ofReal (4 * Real.pi) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  norm_num only [Nat.cast_ofNat]
  rw [he]

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction

private theorem cylindrical_lintegral (g : ℝ × ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p : ℝ × EuclideanSpace ℝ (Fin 2), g (p.1, ‖p.2‖)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ p : ℝ × ℝ in (Complex.equivRealProd.symm ⁻¹' UpperHalfPlane.upperHalfPlaneSet),
        ENNReal.ofReal p.2 * g p := by
  have hm : Measurable (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => g (p.1, ‖p.2‖)) :=
    hg.comp (measurable_fst.prodMk measurable_snd.norm)
  rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
  have he : ∀ z : ℝ, (∫⁻ a : EuclideanSpace ℝ (Fin 2), g (z, ‖a‖)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ r : ℝ in Ioi (0 : ℝ),
        ENNReal.ofReal r * g (z, r) := by
    intro z
    exact norm_lintegral_two (fun r => g (z, r))
      (hg.comp (measurable_const.prodMk measurable_id))
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  have ht : (Complex.equivRealProd.symm ⁻¹' UpperHalfPlane.upperHalfPlaneSet) = (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
    ext p; simp [UpperHalfPlane.upperHalfPlaneSet, Complex.equivRealProd]
  rw [ht, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal p.2 * g p)
      ((measurable_snd.ennreal_ofReal).mul hg).aemeasurable,
    Measure.restrict_univ]

private theorem spherical_lintegral_prod (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : ℝ × EuclideanSpace ℝ (Fin 2),
      F (Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2), p.1 / Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2))) =
    ENNReal.ofReal (2 * Real.pi) * ∫⁻ p : ℝ × ℝ in D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction.domain,
      ENNReal.ofReal (p.1 ^ 2) * F (p.1, p.2) := by
  let g : ℝ × ℝ → ℝ≥0∞ := fun p =>
    F (Real.sqrt (p.1 ^ 2 + p.2 ^ 2), p.1 / Real.sqrt (p.1 ^ 2 + p.2 ^ 2))
  have hg : Measurable g := by dsimp [g]; fun_prop
  rw [cylindrical_lintegral g hg, meridian_change_lintegral]
  congr 1
  apply setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
  intro p hp
  dsimp [g]
  have he : Real.sqrt ((meridian p).1 ^ 2 + (meridian p).2 ^ 2) = p.1 := by
    rw [meridian_norm_square hp, Real.sqrt_sq (show 0 ≤ p.1 from hp.1.le)]
  rw [he]
  congr 2
  congr 1
  change p.1 * p.2 / p.1 = p.2
  field_simp [ne_of_gt (show 0 < p.1 from hp.1)]

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction

namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open scoped RealInnerProductSpace

private def axialSplit : EuclideanSpace ℝ (Fin 3) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
      ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))))

private theorem axialSplit_measurePreserving : MeasurePreserving axialSplit volume volume := by
  apply (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).trans
  apply (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0).trans
  have h := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).symm
  convert h using 1 <;> rfl

private theorem axialSplit_fst (v : EuclideanSpace ℝ (Fin 3)) : (axialSplit v).1 = v 0 := rfl

private theorem axialSplit_norm (v : EuclideanSpace ℝ (Fin 3)) :
    Real.sqrt ((axialSplit v).1 ^ 2 + ‖(axialSplit v).2‖ ^ 2) = ‖v‖ := by
  rw [EuclideanSpace.real_norm_sq_eq, axialSplit_fst]
  have he : (∑ i : Fin 2, ((axialSplit v).2 i) ^ 2) = ∑ i : Fin 2, v i.succ ^ 2 := by
    congr 1
  rw [he]
  have hn := EuclideanSpace.real_norm_sq_eq v
  rw [Fin.sum_univ_succ] at hn
  rw [← hn, Real.sqrt_sq (norm_nonneg v)]

private theorem spherical_lintegral_axis (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v : EuclideanSpace ℝ (Fin 3), F (‖v‖, v 0 / ‖v‖)) =
    ENNReal.ofReal (2 * Real.pi) * ∫⁻ p : ℝ × ℝ in D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction.domain,
      ENNReal.ofReal (p.1 ^ 2) * F (p.1, p.2) := by
  rw [← spherical_lintegral_prod F hF]
  let g : ℝ × EuclideanSpace ℝ (Fin 2) → ℝ≥0∞ := fun p =>
    F (Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2), p.1 / Real.sqrt (p.1 ^ 2 + ‖p.2‖ ^ 2))
  have hg : Measurable g := by dsimp [g]; fun_prop
  have he := axialSplit_measurePreserving.lintegral_comp hg
  change (∫⁻ a : EuclideanSpace ℝ (Fin 3), F (Real.sqrt ((axialSplit a).1 ^ 2 + ‖(axialSplit a).2‖ ^ 2), (axialSplit a).1 / Real.sqrt ((axialSplit a).1 ^ 2 + ‖(axialSplit a).2‖ ^ 2))) = _ at he
  simp_rw [axialSplit_norm, axialSplit_fst] at he
  exact he

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open scoped RealInnerProductSpace

private def axisReflection (a : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  Submodule.reflection (ℝ ∙ (a - (fun r : ℝ => (PiLp.single 2 0 r : EuclideanSpace ℝ (Fin 3))) ‖a‖))ᗮ

private theorem axisReflection_self (a : EuclideanSpace ℝ (Fin 3)) :
    axisReflection a a = (fun r : ℝ => (PiLp.single 2 0 r : EuclideanSpace ℝ (Fin 3))) ‖a‖ := by
  apply Submodule.reflection_sub
  simp

private theorem axisReflection_inner (a b : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ a (axisReflection a b) = ‖a‖ * b 0 := by
  have he := (axisReflection a).inner_map_map a (axisReflection a b)
  rw [axisReflection_self] at he
  have hh : axisReflection a (axisReflection a b) = b :=
    Submodule.reflection_reflection _ _
  rw [hh] at he
  rw [← he, EuclideanSpace.inner_single_left]
  simp

private theorem norm_mul_cosine (a b : EuclideanSpace ℝ (Fin 3)) :
    ‖a‖ * ‖b‖ * (b 0 / ‖b‖) = ‖a‖ * b 0 := by
  by_cases hb : b = 0
  · simp [hb]
  · have hn : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
    field_simp

private theorem spherical_lintegral_inner (a : EuclideanSpace ℝ (Fin 3))
    (F : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ b : EuclideanSpace ℝ (Fin 3), F (‖b‖, inner ℝ a b)) =
    ENNReal.ofReal (2 * Real.pi) * ∫⁻ p : ℝ × ℝ in D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction.domain,
      ENNReal.ofReal (p.1 ^ 2) * F (p.1, ‖a‖ * p.1 * p.2) := by
  let g : EuclideanSpace ℝ (Fin 3) → ℝ≥0∞ := fun b => F (‖b‖, inner ℝ a b)
  have hg : Measurable g := by dsimp [g]; fun_prop
  have he := (axisReflection a).measurePreserving.lintegral_comp hg
  change (∫⁻ b : EuclideanSpace ℝ (Fin 3),
    F (‖axisReflection a b‖, inner ℝ a (axisReflection a b))) = _ at he
  simp_rw [(axisReflection a).norm_map, axisReflection_inner] at he
  rw [← he]
  let G : ℝ × ℝ → ℝ≥0∞ := fun p => F (p.1, ‖a‖ * p.1 * p.2)
  have hG : Measurable G := by dsimp [G]; fun_prop
  have hs := spherical_lintegral_axis G hG
  simp only [G, norm_mul_cosine] at hs
  exact hs

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open scoped RealInnerProductSpace

private theorem relative_cosine_lintegral (F : ℝ × ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ b : EuclideanSpace ℝ (Fin 3),
      F (‖a‖, ‖b‖, inner ℝ a b)) =
    ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ r : ℝ in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 2) *
        ∫⁻ p : ℝ × ℝ in D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction.domain,
          ENNReal.ofReal (p.1 ^ 2) * F (r, p.1, r * p.1 * p.2) := by
  have he : ∀ a : EuclideanSpace ℝ (Fin 3),
      (∫⁻ b : EuclideanSpace ℝ (Fin 3), F (‖a‖, ‖b‖, inner ℝ a b)) =
      ENNReal.ofReal (2 * Real.pi) * ∫⁻ p : ℝ × ℝ in D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction.domain,
        ENNReal.ofReal (p.1 ^ 2) * F (‖a‖, p.1, ‖a‖ * p.1 * p.2) := by
    intro a
    exact spherical_lintegral_inner a (fun p => F (‖a‖, p.1, p.2))
      (hF.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  let g : ℝ → ℝ≥0∞ := fun r => ∫⁻ p : ℝ × ℝ in D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction.domain,
      ENNReal.ofReal (p.1 ^ 2) * F (r, p.1, r * p.1 * p.2)
  have hg : Measurable g := by
    apply Measurable.lintegral_prod_right
    exact (measurable_snd.fst.pow_const 2).ennreal_ofReal.mul
      (hF.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
        ((measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd))))
  rw [norm_lintegral_three g hg]
  dsimp [g]
  ring

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction

namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open Classical
open D5.S3.Quantum.Measurement.OrderedRootCoordinates D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open scoped RealInnerProductSpace

private def interiorPositiveSector : Set ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) := {q |
    0 < q.1.1 ∧ 0 < q.2.1 ∧ 0 < ‖q.1.2‖ ∧ 0 < ‖q.2.2‖ ∧
    q.1.1 + ‖q.1.2‖ < 1 ∧ q.2.1 + ‖q.2.2‖ < 1 ∧
    (inner ℝ q.1.2 q.2.2 - q.1.1 * q.2.1) ^ 2 <
      (1 - hYu q.1.1 q.1.2 ^ 2 - hYu q.2.1 q.2.2 ^ 2) *
        (1 - q.1.1 ^ 2 / hYu q.1.1 q.1.2 ^ 2 -
          q.2.1 ^ 2 / hYu q.2.1 q.2.2 ^ 2)}

private theorem measurableSet_interiorPositiveSector : MeasurableSet interiorPositiveSector := by
  unfold interiorPositiveSector hYu
  measurability

private theorem null_lift_first (S : Set (ℝ × EuclideanSpace ℝ (Fin 3))) (hS : volume S = 0) :
    volume {q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) | q.1 ∈ S} = 0 := by
  have he : {q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) | q.1 ∈ S} = S ×ˢ univ := by ext q; simp
  rw [he, Measure.volume_eq_prod, Measure.prod_prod, hS, zero_mul]

private theorem null_lift_second (S : Set (ℝ × EuclideanSpace ℝ (Fin 3))) (hS : volume S = 0) :
    volume {q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) | q.2 ∈ S} = 0 := by
  have he : {q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) | q.2 ∈ S} = univ ×ˢ S := by ext q; simp
  rw [he, Measure.volume_eq_prod, Measure.prod_prod, hS, mul_zero]

private theorem volume_positiveSector_eq_interior :
    volume positiveSector = volume interiorPositiveSector := by
  have hb1 := null_lift_first _ body_boundary_null
  have hb2 := null_lift_second _ body_boundary_null
  have hz1 := null_lift_first _ vector_zero_null
  have hz2 := null_lift_second _ vector_zero_null
  apply measure_congr
  have h1 : ∀ᵐ q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))), ¬ (|q.1.1| + ‖q.1.2‖ = 1) := by
    rw [ae_iff]; simpa only [not_not, mem_ofPred_eq] using hb1
  have h2 : ∀ᵐ q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))), ¬ (|q.2.1| + ‖q.2.2‖ = 1) := by
    rw [ae_iff]; simpa only [not_not, mem_ofPred_eq] using hb2
  have h3 : ∀ᵐ q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))), q.1.2 ≠ 0 := by
    rw [ae_iff]; simpa only [not_not, mem_ofPred_eq] using hz1
  have h4 : ∀ᵐ q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))), q.2.2 ≠ 0 := by
    rw [ae_iff]; simpa only [not_not, mem_ofPred_eq] using hz2
  filter_upwards [h1, h2, h3, h4] with q hb1 hb2 hz1 hz2
  apply propext
  simp only [positiveSector, NJM, V, interiorPositiveSector, mem_inter_iff, mem_ofPred_eq]
  change ¬ (|q.1.1| + ‖q.1.2‖ = 1) at hb1
  change ¬ (|q.2.1| + ‖q.2.2‖ = 1) at hb2
  change q.1.2 ≠ 0 at hz1
  change q.2.2 ≠ 0 at hz2
  have hn1 : 0 < ‖q.1.2‖ := norm_pos_iff.mpr hz1
  have hn2 : 0 < ‖q.2.2‖ := norm_pos_iff.mpr hz2
  constructor
  · rintro ⟨⟨hV1, hV2, hC⟩, hx, hy⟩
    rw [abs_of_pos hx] at hV1 hb1
    rw [abs_of_pos hy] at hV2 hb2
    exact ⟨hx, hy, hn1, hn2, lt_of_le_of_ne hV1 hb1, lt_of_le_of_ne hV2 hb2, hC⟩
  · rintro ⟨hx, hy, hr, hq, hV1, hV2, hC⟩
    refine ⟨⟨?_, ?_, hC⟩, hx, hy⟩
    · simpa only [abs_of_pos hx] using hV1.le
    · simpa only [abs_of_pos hy] using hV2.le

private def radialCriterion (x y : ℝ) (p : ℝ × ℝ × ℝ) : Prop :=
    0 < x ∧ 0 < y ∧ 0 < p.1 ∧ 0 < p.2.1 ∧
    x + p.1 < 1 ∧ y + p.2.1 < 1 ∧
    (p.2.2 - x*y)^2 <
      (1 - (fun x r : ℝ => hYu x (PiLp.single 2 0 r)) x p.1 ^ 2 - (fun x r : ℝ => hYu x (PiLp.single 2 0 r)) y p.2.1 ^ 2) *
      (1 - x^2 / (fun x r : ℝ => hYu x (PiLp.single 2 0 r)) x p.1 ^ 2 - y^2 / (fun x r : ℝ => hYu x (PiLp.single 2 0 r)) y p.2.1 ^ 2)

private def radialKernel (x y : ℝ) (p : ℝ × ℝ × ℝ) : ℝ≥0∞ :=
    if radialCriterion x y p then 1 else 0

private theorem radialKernel_measurable :
    Measurable (fun p : ℝ × ℝ × ℝ × ℝ × ℝ => radialKernel p.1 p.2.1 p.2.2) := by
  unfold radialKernel
  apply Measurable.ite
  · unfold radialCriterion hYu
    simp only [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
    measurability
  · exact measurable_const
  · exact measurable_const

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open D5.S3.Quantum.Measurement.OrderedRootCoordinates D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open scoped RealInnerProductSpace

private theorem volume_positiveSector_radial :
    volume positiveSector = ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ x : ℝ, ∫⁻ y : ℝ,
        ∫⁻ r : ℝ in Ioi (0 : ℝ), ENNReal.ofReal (r^2) *
          ∫⁻ p : ℝ × ℝ in D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction.domain,
            ENNReal.ofReal (p.1^2) * radialKernel x y (r,p.1,r*p.1*p.2) := by
  let H : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))) → ℝ≥0∞ := interiorPositiveSector.indicator (fun _ => 1)
  have hH : Measurable H := measurable_const.indicator measurableSet_interiorPositiveSector
  have hsplit : volume positiveSector =
      ∫⁻ x : ℝ, ∫⁻ a : EuclideanSpace ℝ (Fin 3),
        ∫⁻ y : ℝ, ∫⁻ b : EuclideanSpace ℝ (Fin 3), H ((x,a),(y,b)) := by
    rw [volume_positiveSector_eq_interior]
    change _ = ∫⁻ x : ℝ, ∫⁻ a : EuclideanSpace ℝ (Fin 3),
      ∫⁻ y : ℝ, ∫⁻ b : EuclideanSpace ℝ (Fin 3), H ((x,a),(y,b))
    rw [← lintegral_indicator_one measurableSet_interiorPositiveSector]
    change (∫⁻ q : ((ℝ × EuclideanSpace ℝ (Fin 3)) × (ℝ × EuclideanSpace ℝ (Fin 3))), H q) = _
    rw [Measure.volume_eq_prod, lintegral_prod _ hH.aemeasurable]
    rw [Measure.volume_eq_prod, lintegral_prod _ hH.lintegral_prod_right'.aemeasurable]
    apply lintegral_congr
    intro x
    apply lintegral_congr
    intro a
    exact lintegral_prod (fun p : (ℝ × EuclideanSpace ℝ (Fin 3)) => H ((x,a),p))
      ((hH.comp (measurable_const.prodMk measurable_id)).aemeasurable)
  rw [hsplit]
  have hswap : ∀ x : ℝ,
      (∫⁻ a : EuclideanSpace ℝ (Fin 3), ∫⁻ y : ℝ,
        ∫⁻ b : EuclideanSpace ℝ (Fin 3), H ((x,a),(y,b))) =
      ∫⁻ y : ℝ, ∫⁻ a : EuclideanSpace ℝ (Fin 3),
        ∫⁻ b : EuclideanSpace ℝ (Fin 3), H ((x,a),(y,b)) := by
    intro x
    apply lintegral_lintegral_swap
    apply Measurable.aemeasurable
    apply Measurable.lintegral_prod_right
    exact hH.comp ((measurable_const.prodMk measurable_fst.fst).prodMk
      (measurable_fst.snd.prodMk measurable_snd))
  simp_rw [hswap]
  change (∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ a : EuclideanSpace ℝ (Fin 3),
    ∫⁻ b : EuclideanSpace ℝ (Fin 3), interiorPositiveSector.indicator (fun _ => 1) ((x,a),(y,b))) = _
  have hKernel (x y : ℝ) (a b : EuclideanSpace ℝ (Fin 3)) :
      radialKernel x y (‖a‖, ‖b‖, inner ℝ a b) =
        interiorPositiveSector.indicator (fun _ => (1 : ℝ≥0∞)) ((x,a),(y,b)) := by
    simp only [radialKernel, radialCriterion, hYu, PiLp.norm_single, Real.norm_eq_abs,
      sq_abs, interiorPositiveSector, indicator_apply, mem_ofPred_eq]
  simp_rw [← hKernel]
  have hxy : ∀ x y : ℝ, Measurable (radialKernel x y) := by
    intro x y
    exact radialKernel_measurable.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  simp_rw [relative_cosine_lintegral _ (hxy _ _)]
  simp_rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open D5.S3.Quantum.Measurement.OrderedRootCoordinates D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open scoped RealInnerProductSpace

@[fun_prop] private theorem measurable_radialKernel {α : Type*} [MeasurableSpace α]
    {x y r q z : α → ℝ} (hx : Measurable x) (hy : Measurable y)
    (hr : Measurable r) (hq : Measurable q) (hz : Measurable z) :
    Measurable (fun a => radialKernel (x a) (y a) (r a, q a, z a)) :=
  radialKernel_measurable.comp (hx.prodMk (hy.prodMk (hr.prodMk (hq.prodMk hz))))

private theorem angular_domain_split (x y r : ℝ) :
    (∫⁻ p : ℝ × ℝ in D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction.domain,
      ENNReal.ofReal (p.1^2) * radialKernel x y (r,p.1,r*p.1*p.2)) =
    ∫⁻ q : ℝ in Ioi (0 : ℝ), ENNReal.ofReal (q^2) *
      ∫⁻ s : ℝ in Ioo (-1 : ℝ) 1, radialKernel x y (r,q,r*q*s) := by
  rw [D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction.domain, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [lintegral_prod _ (by fun_prop)]
  apply lintegral_congr
  intro q
  dsimp only
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem volume_positiveSector_radial_regroup :
    volume positiveSector = ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ x : ℝ, ∫⁻ r : ℝ in Ioi (0 : ℝ),
        ∫⁻ y : ℝ, ∫⁻ q : ℝ in Ioi (0 : ℝ),
          ENNReal.ofReal (r^2) * ENNReal.ofReal (q^2) *
            ∫⁻ s : ℝ in Ioo (-1 : ℝ) 1, radialKernel x y (r,q,r*q*s) := by
  rw [volume_positiveSector_radial]
  simp_rw [angular_domain_split]
  congr 1
  apply lintegral_congr
  intro x
  rw [lintegral_lintegral_swap (by fun_prop)]
  apply lintegral_congr
  intro r
  apply lintegral_congr
  intro y
  rw [← lintegral_const_mul' (ENNReal.ofReal (r^2))
    (fun q : ℝ => ENNReal.ofReal (q^2) * ∫⁻ s : ℝ in Ioo (-1 : ℝ) 1,
      radialKernel x y (r,q,r*q*s)) ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro q
  exact (mul_assoc _ _ _).symm

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open Classical D5.S3.Quantum.Measurement.OrderedRootCoordinates

private def scalarCriterion (p q : ℝ × ℝ) (s : ℝ) : Prop :=
    (p.2*q.2*s-p.1*q.1)^2 <
      (1-(fun x r : ℝ => hYu x (PiLp.single 2 0 r)) p.1 p.2^2-(fun x r : ℝ => hYu x (PiLp.single 2 0 r)) q.1 q.2^2) *
      (1-p.1^2/(fun x r : ℝ => hYu x (PiLp.single 2 0 r)) p.1 p.2^2-q.1^2/(fun x r : ℝ => hYu x (PiLp.single 2 0 r)) q.1 q.2^2)

private def angularIntegral (p q : ℝ × ℝ) : ℝ≥0∞ :=
    ∫⁻ s : ℝ in Ioo (-1 : ℝ) 1, if scalarCriterion p q s then 1 else 0

@[fun_prop] private theorem angularIntegral_measurable : Measurable (Function.uncurry angularIntegral) := by
  apply Measurable.lintegral_prod_right
  apply Measurable.ite
  · unfold scalarCriterion hYu
    simp only [PiLp.norm_single, Real.norm_eq_abs, sq_abs]
    measurability
  · exact measurable_const
  · exact measurable_const

private theorem angularIntegral_eq_volume (p q : ℝ × ℝ) :
    angularIntegral p q = volume {s : ℝ | -1 ≤ s ∧ s ≤ 1 ∧ scalarCriterion p q s} := by
  have hm : MeasurableSet {s : ℝ | scalarCriterion p q s} := by
    unfold scalarCriterion hYu
    simp only [PiLp.norm_single, Real.norm_eq_abs, sq_abs]; measurability
  unfold angularIntegral
  rw [Measure.restrict_congr_set (Ioo_ae_eq_Icc : Ioo (-1 : ℝ) 1 =ᵐ[volume] Icc (-1 : ℝ) 1)]
  have he : (fun s : ℝ => if scalarCriterion p q s then (1 : ℝ≥0∞) else 0) =
      {s : ℝ | scalarCriterion p q s}.indicator (fun _ => (1 : ℝ≥0∞)) := by
    ext s; simp only [indicator_apply, mem_ofPred_eq]
  rw [he, lintegral_indicator_const hm, one_mul, Measure.restrict_apply hm]
  congr 1
  ext s
  simp [and_comm, and_left_comm, and_assoc]

private theorem radialKernel_body_indicator (p q : ℝ × ℝ) (s : ℝ) :
    radialKernel p.1 q.1 (p.2,q.2,p.2*q.2*s) =
      radialBody.indicator (fun p => radialBody.indicator
        (fun q => if scalarCriterion p q s then (1 : ℝ≥0∞) else 0) q) p := by
  unfold radialKernel radialCriterion scalarCriterion radialBody
  simp only [indicator_apply, mem_ofPred_eq]
  by_cases hp : 0<p.1 ∧ 0<p.2 ∧ p.1+p.2<1
  · by_cases hq : 0<q.1 ∧ 0<q.2 ∧ q.1+q.2<1
    · simp only [if_pos hp, if_pos hq]
      congr 1
      apply propext
      tauto
    · rw [if_pos hp, if_neg hq, if_neg]
      tauto
  · rw [if_neg hp, if_neg]
    tauto

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open Classical D5.S3.Quantum.Measurement.OrderedRootCoordinates

private theorem measurableSet_radialBody : MeasurableSet radialBody := by
  unfold radialBody; measurability

private def weightedAngular (p q : ℝ × ℝ) : ℝ≥0∞ :=
    ENNReal.ofReal (p.2^2) * ENNReal.ofReal (q.2^2) * angularIntegral p q

@[fun_prop] private theorem weightedAngular_measurable : Measurable (Function.uncurry weightedAngular) := by
  exact (measurable_fst.snd.pow_const 2).ennreal_ofReal.mul
    (measurable_snd.snd.pow_const 2).ennreal_ofReal |>.mul angularIntegral_measurable

private theorem weighted_kernel_body (p q : ℝ × ℝ) :
    ENNReal.ofReal (p.2^2) * ENNReal.ofReal (q.2^2) *
      (∫⁻ s : ℝ in Ioo (-1 : ℝ) 1, radialKernel p.1 q.1 (p.2,q.2,p.2*q.2*s)) =
    radialBody.indicator (fun p => radialBody.indicator (weightedAngular p) q) p := by
  simp_rw [radialKernel_body_indicator]
  by_cases hp : p ∈ radialBody
  · by_cases hq : q ∈ radialBody
    · simp only [indicator_of_mem hp, indicator_of_mem hq]
      rfl
    · simp [indicator_of_mem hp, indicator_of_notMem hq]
  · simp [indicator_of_notMem hp]

private theorem radialBody_fubini (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p : ℝ × ℝ in radialBody, f p) =
      ∫⁻ x : ℝ, ∫⁻ r : ℝ in Ioi (0 : ℝ), radialBody.indicator f (x,r) := by
  have hm := hf.indicator measurableSet_radialBody
  have hs : Function.support (radialBody.indicator f) ⊆ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) := by
    intro p hp
    have hb : p ∈ radialBody := by
      by_contra hn
      exact hp (indicator_of_notMem hn f)
    exact ⟨mem_univ _, hb.2.1⟩
  rw [← lintegral_indicator measurableSet_radialBody]
  rw [← setLIntegral_eq_of_support_subset hs]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
    lintegral_prod _ hm.aemeasurable]

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open Classical D5.S3.Quantum.Measurement.OrderedRootCoordinates

set_option maxHeartbeats 1000000 in
private theorem volume_positiveSector_radialBody :
    volume positiveSector = ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ p : ℝ × ℝ in radialBody, ∫⁻ q : ℝ × ℝ in radialBody, weightedAngular p q := by
  rw [volume_positiveSector_radial_regroup]
  have hh : ∀ x r y q : ℝ, ENNReal.ofReal (r^2)*ENNReal.ofReal (q^2)*
      (∫⁻ s : ℝ in Ioo (-1 : ℝ) 1, radialKernel x y (r,q,r*q*s)) =
      radialBody.indicator (fun p => radialBody.indicator (weightedAngular p) (y,q)) (x,r) :=
    fun x r y q => weighted_kernel_body (x,r) (y,q)
  simp_rw [hh]
  congr 1
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => ∫⁻ q : ℝ × ℝ in radialBody, weightedAngular p q
  have hF : Measurable F := weightedAngular_measurable.lintegral_prod_right
  have he : ∀ x r : ℝ,
      (∫⁻ y : ℝ, ∫⁻ q : ℝ in Ioi (0 : ℝ),
        radialBody.indicator (fun p => radialBody.indicator (weightedAngular p) (y,q)) (x,r)) =
      radialBody.indicator F (x,r) := by
    intro x r
    by_cases hp : (x,r) ∈ radialBody
    · simp only [indicator_of_mem hp]
      exact (radialBody_fubini (weightedAngular (x,r))
        (weightedAngular_measurable.comp (measurable_const.prodMk measurable_id))).symm
    · simp only [indicator_of_notMem hp, lintegral_zero]
  simp_rw [he]
  exact (radialBody_fubini F hF).symm

private def coordinateJacobian (p : ℝ × ℝ) : ℝ :=
    (p.1-p.2)/(4*xCoord p.1 p.2*rCoord p.1 p.2)

private theorem volume_positiveSector_ordered :
    volume positiveSector = ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ p : ℝ × ℝ in rootDomain, ∫⁻ q : ℝ × ℝ in rootDomain,
        ENNReal.ofReal (coordinateJacobian p) * ENNReal.ofReal (coordinateJacobian q) *
          weightedAngular (coordinateMap p) (coordinateMap q) := by
  rw [volume_positiveSector_radialBody, coordinate_change_lintegral]
  congr 1
  apply lintegral_congr
  intro p
  rw [coordinate_change_lintegral]
  change ENNReal.ofReal (coordinateJacobian p) *
    (∫⁻ q : ℝ × ℝ in rootDomain, ENNReal.ofReal (coordinateJacobian q) *
      weightedAngular (coordinateMap p) (coordinateMap q)) = _
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro q
  exact (mul_assoc _ _ _).symm

private theorem angularIntegral_coordinates {p q : ℝ × ℝ}
    (hp : p ∈ rootDomain) (hq : q ∈ rootDomain) :
    angularIntegral (coordinateMap p) (coordinateMap q) =
      if 0 < 1-p.1-q.1 then
        ENNReal.ofReal (2*Real.sqrt ((1-p.1-q.1)*(1-p.2-q.2)) /
          (rCoord p.1 p.2*rCoord q.1 q.2)) else 0 := by
  have hp' : 0<p.2 ∧ p.2<p.1 ∧ p.1<1 := hp
  have hq' : 0<q.2 ∧ q.2<q.1 ∧ q.1<1 := hq
  have hpr := root_coordinates hp'.1.le hp'.2.1.le hp'.2.2.le (hp'.1.trans hp'.2.1)
  have hqr := root_coordinates hq'.1.le hq'.2.1.le hq'.2.2.le (hq'.1.trans hq'.2.1)
  rw [angularIntegral_eq_volume]
  unfold scalarCriterion coordinateMap
  dsimp only
  simp_rw [hpr.2, hqr.2, hpr.1, hqr.1]
  exact angular_volume_ordered hp'.1.le hp'.2.1.le hp'.2.2.le hq'.1.le hq'.2.1.le hq'.2.2.le

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
namespace D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
open Classical D5.S3.Quantum.Measurement.OrderedRootCoordinates

def rootDensity (p q : ℝ × ℝ) : ℝ :=
    if 0<1-p.1-q.1 then
      (p.1-p.2)*(q.1-q.2)*Real.sqrt ((1-p.1-q.1)*(1-p.2-q.2)) /
        (xCoord p.1 p.2*xCoord q.1 q.2) else 0

def rootI : ℝ≥0∞ := ∫⁻ p : ℝ × ℝ in rootDomain,
    ∫⁻ q : ℝ × ℝ in rootDomain, ENNReal.ofReal (rootDensity p q)

private theorem coordinateJacobian_pos {p : ℝ × ℝ} (hp : p ∈ rootDomain) :
    0 < coordinateJacobian p := by
  have hp' : 0<p.2 ∧ p.2<p.1 ∧ p.1<1 := hp
  have hu0 := hp'.1.trans hp'.2.1
  have hv0 : 0<p.2 := hp'.1
  unfold coordinateJacobian xCoord rCoord
  apply div_pos (sub_pos.mpr hp'.2.1)
  have h1 : 0<1-p.1 := sub_pos.mpr hp'.2.2
  have h2 : 0<1-p.2 := sub_pos.mpr (hp'.2.1.trans hp'.2.2)
  positivity

private theorem coordinate_weight_cancellation {p q : ℝ × ℝ}
    (hp : p ∈ rootDomain) (hq : q ∈ rootDomain) :
    ENNReal.ofReal (coordinateJacobian p) * ENNReal.ofReal (coordinateJacobian q) *
      weightedAngular (coordinateMap p) (coordinateMap q) =
    ENNReal.ofReal (1/8) * ENNReal.ofReal (rootDensity p q) := by
  have hp' : 0<p.2 ∧ p.2<p.1 ∧ p.1<1 := hp
  have hq' : 0<q.2 ∧ q.2<q.1 ∧ q.1<1 := hq
  have hxp : 0 < xCoord p.1 p.2 := by
    unfold xCoord; exact mul_pos (Real.sqrt_pos.mpr (hp'.1.trans hp'.2.1)) (Real.sqrt_pos.mpr hp'.1)
  have hxq : 0 < xCoord q.1 q.2 := by
    unfold xCoord; exact mul_pos (Real.sqrt_pos.mpr (hq'.1.trans hq'.2.1)) (Real.sqrt_pos.mpr hq'.1)
  have hrp : 0 < rCoord p.1 p.2 := by
    unfold rCoord; exact mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr hp'.2.2))
      (Real.sqrt_pos.mpr (sub_pos.mpr (hp'.2.1.trans hp'.2.2)))
  have hrq : 0 < rCoord q.1 q.2 := by
    unfold rCoord; exact mul_pos (Real.sqrt_pos.mpr (sub_pos.mpr hq'.2.2))
      (Real.sqrt_pos.mpr (sub_pos.mpr (hq'.2.1.trans hq'.2.2)))
  unfold weightedAngular
  rw [angularIntegral_coordinates hp hq]
  unfold rootDensity
  by_cases hA : 0 < 1-p.1-q.1
  · rw [if_pos hA, if_pos hA]
    change ENNReal.ofReal (coordinateJacobian p) * ENNReal.ofReal (coordinateJacobian q) *
      (ENNReal.ofReal (rCoord p.1 p.2^2) * ENNReal.ofReal (rCoord q.1 q.2^2) *
        ENNReal.ofReal (2*Real.sqrt ((1-p.1-q.1)*(1-p.2-q.2)) /
          (rCoord p.1 p.2*rCoord q.1 q.2))) = _
    simp only [mul_assoc]
    rw [← ENNReal.ofReal_mul (sq_nonneg (rCoord q.1 q.2)),
      ← ENNReal.ofReal_mul (sq_nonneg (rCoord p.1 p.2)),
      ← ENNReal.ofReal_mul (coordinateJacobian_pos hq).le,
      ← ENNReal.ofReal_mul (coordinateJacobian_pos hp).le,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/8)]
    congr 1
    unfold coordinateJacobian
    field_simp [ne_of_gt hxp, ne_of_gt hxq, ne_of_gt hrp, ne_of_gt hrq]
    <;> ring
  · simp [hA]

theorem volume_NJM_rootI : volume NJM = ENNReal.ofReal (4*Real.pi^2) * rootI := by
  rw [volume_NJM_four_sectors, volume_positiveSector_ordered]
  have he : (∫⁻ p : ℝ × ℝ in rootDomain, ∫⁻ q : ℝ × ℝ in rootDomain,
        ENNReal.ofReal (coordinateJacobian p) * ENNReal.ofReal (coordinateJacobian q) *
          weightedAngular (coordinateMap p) (coordinateMap q)) = ENNReal.ofReal (1/8) * rootI := by
    calc
      _ = ∫⁻ p : ℝ × ℝ in rootDomain, ∫⁻ q : ℝ × ℝ in rootDomain,
          ENNReal.ofReal (1/8) * ENNReal.ofReal (rootDensity p q) := by
        apply setLIntegral_congr_fun measurableSet_rootDomain
        intro p hp
        apply setLIntegral_congr_fun measurableSet_rootDomain
        intro q hq
        exact coordinate_weight_cancellation hp hq
      _ = _ := by
        unfold rootI
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [he]
  have hc : (4 : ℝ≥0∞) * (ENNReal.ofReal (4*Real.pi) * ENNReal.ofReal (2*Real.pi)) *
      ENNReal.ofReal (1/8) = ENNReal.ofReal (4*Real.pi^2) := by
    rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ)≤4*Real.pi),
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc
    _ = ((4 : ℝ≥0∞) * (ENNReal.ofReal (4*Real.pi) * ENNReal.ofReal (2*Real.pi)) *
      ENNReal.ofReal (1/8)) * rootI := by ring
    _ = _ := by rw [hc]

end D5.S3.Quantum.Measurement.QubitIncompatibilityRadialReduction
