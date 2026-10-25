import D5.S3.Geometry.Hyperideal.CFMPNormalizedHausdorffDimension435Transient
import D5.S3.Geometry.HyperbolicPlaneRealization
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped NNReal ENNReal
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicPlaneRealization
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicNormalizedDensity
open CFMPNormalizedHausdorffDimension435Transient

namespace CFMPVerticalNative2Density435Transient

private local instance : MeasurableSpace (UpperHalfSpace ℂ) := borel _
private local instance : BorelSpace (UpperHalfSpace ℂ) := ⟨rfl⟩
private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

abbrev EuclideanPlane := {z : ℂ // 0 < z.im}

def underlying : UpperHalfPlane ≃ₜ EuclideanPlane :=
  UpperHalfPlane.isEmbedding_coe.toHomeomorph.trans
    (Homeomorph.setCongr UpperHalfPlane.range_coe)

def euclideanEmbedding (z : ℂ) : WithLp 2 (ℂ × ℝ) :=
  WithLp.toLp 2 (Complex.mk z.re 0, z.im)

def coordinateEmbedding (z : EuclideanPlane) : UpperHalfSpace ℂ :=
  ⟨euclideanEmbedding z.val, z.property⟩

theorem euclideanEmbedding_isometry : Isometry euclideanEmbedding := by
  apply Isometry.of_dist_eq
  intro z w
  rw [euclideanEmbedding, euclideanEmbedding, WithLp.prod_dist_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd]
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
  simp [Real.dist_eq, sq_abs, Real.sq_sqrt (sq_nonneg _)]

theorem coordinateEmbedding_isometry : Isometry coordinateEmbedding := by
  apply Isometry.of_dist_eq
  intro z w
  exact euclideanEmbedding_isometry.dist_eq z.val w.val

theorem coordinateEmbedding_range :
    range coordinateEmbedding = {p : UpperHalfSpace ℂ | p.val.fst.im = 0} := by
  ext p
  constructor
  · rintro ⟨z, rfl⟩
    change (Complex.mk z.val.re 0).im = 0
    rfl
  · intro hp
    refine ⟨⟨Complex.mk p.val.fst.re p.val.snd, p.property⟩, ?_⟩
    apply Subtype.ext
    apply (WithLp.ofLp_injective 2)
    apply Prod.ext
    · apply Complex.ext
      · rfl
      · exact hp.symm
    · rfl

theorem coordinateEmbedding_measurableEmbedding :
    MeasurableEmbedding coordinateEmbedding := by
  apply coordinateEmbedding_isometry.isEmbedding.measurableEmbedding
  rw [coordinateEmbedding_range]
  exact (isClosed_eq
    (Complex.continuous_im.comp ((WithLp.continuous_fst 2 ℂ ℝ).comp continuous_subtype_val))
    continuous_const).measurableSet

theorem vertical_isometry : Isometry vertical := by
  apply Isometry.of_dist_eq
  intro z w
  apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
  have h := vertical_cosh z w
  rw [lift_cosh] at h
  exact neg_injective h

theorem same_vertical (z : UpperHalfPlane) :
    HyperbolicSpace.mk (coordinateEmbedding (underlying z)) = vertical z := rfl

private theorem image_lintegral
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (f : X → Y) (hf : Isometry f) (hm : MeasurableEmbedding f)
    (w : Y → ℝ≥0∞) (B : Set X) :
    (∫⁻ y in f '' B, w y ∂(Measure.euclideanHausdorffMeasure 2 : Measure Y)) =
      ∫⁻ x in B, w (f x) ∂(Measure.euclideanHausdorffMeasure 2 : Measure X) := by
  let hp : MeasurePreserving f (Measure.euclideanHausdorffMeasure 2)
      ((Measure.euclideanHausdorffMeasure 2).restrict (range f)) :=
    ⟨hm.measurable, hf.map_euclideanHausdorffMeasure⟩
  have h := hp.setLIntegral_comp_emb hm w B
  rw [Measure.restrict_restrict_of_subset (image_subset_range f B)] at h
  exact h.symm

theorem native_h2_density (A : Set UpperHalfPlane) (hA : MeasurableSet A) :
    (Measure.euclideanHausdorffMeasure 2 : Measure UpperHalfPlane) A =
      ∫⁻ z in UpperHalfPlane.coe '' A,
        ENNReal.ofReal ((z.im)⁻¹ ^ (2 : ℕ)) ∂(volume : Measure ℂ) := by
  let B : Set EuclideanPlane := underlying '' A
  let E : Set (UpperHalfSpace ℂ) := coordinateEmbedding '' B
  let wc : UpperHalfSpace ℂ → ℝ≥0∞ :=
    fun p => ENNReal.ofReal ((height p)⁻¹ ^ (2 : ℕ))
  let wp : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal ((z.im)⁻¹ ^ (2 : ℕ))
  have hB : MeasurableSet B := underlying.toMeasurableEquiv.measurableEmbedding.measurableSet_image.mpr hA
  have hE : MeasurableSet E := coordinateEmbedding_measurableEmbedding.measurableSet_image.mpr hB
  have hpre : coordinatesEquiv ⁻¹' E = HyperbolicSpace.mk '' E := by
    ext p
    constructor
    · intro hp
      exact ⟨p.coordinates, hp, rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact hp
  have hsurf : (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
      (HyperbolicSpace.mk '' E) =
      ∫⁻ p in E, wc p ∂(Measure.euclideanHausdorffMeasure 2 : Measure (UpperHalfSpace ℂ)) := by
    have h := congrArg (fun μ : Measure (UpperHalfSpace ℂ) => μ E)
      (normalized_native_density_nat 2)
    rw [Measure.map_apply coordinatesEquiv.measurable hE, hpre, withDensity_apply _ hE] at h
    exact h
  have hmk : HyperbolicSpace.mk '' E = vertical '' A := by
    dsimp [E,B]
    rw [image_image,image_image]
    rfl
  have hco : MeasurableEmbedding (Subtype.val : EuclideanPlane → ℂ) :=
    MeasurableEmbedding.subtype_coe
      (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  have hcal : (Measure.euclideanHausdorffMeasure 2 : Measure ℂ) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℂ))
  calc
    _ = (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) (vertical '' A) :=
      (vertical_isometry.euclideanHausdorffMeasure_image A).symm
    _ = ∫⁻ p in E, wc p ∂(Measure.euclideanHausdorffMeasure 2 : Measure (UpperHalfSpace ℂ)) := by
      rw [← hmk]
      exact hsurf
    _ = ∫⁻ z in B, wp z.val ∂(Measure.euclideanHausdorffMeasure 2 : Measure EuclideanPlane) :=
      image_lintegral coordinateEmbedding coordinateEmbedding_isometry
        coordinateEmbedding_measurableEmbedding wc B
    _ = ∫⁻ z in Subtype.val '' B, wp z ∂(volume : Measure ℂ) := by
      rw [← hcal]
      exact (image_lintegral Subtype.val isometry_subtype_coe hco wp B).symm
    _ = _ := by
      dsimp [B,wp]
      rw [image_image]
      rfl

theorem native_h2_eq_volume :
    (Measure.euclideanHausdorffMeasure 2 : Measure UpperHalfPlane) = volume := by
  ext A hA
  rw [native_h2_density A hA, UpperHalfPlane.volume_eq_lintegral A]
  apply setLIntegral_congr_fun (UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hA)
  rintro _ ⟨z,hz,rfl⟩
  dsimp only
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  simp [NNReal.coe_pow, NNReal.coe_div, Real.norm_eq_abs, abs_of_pos z.im_pos, one_div]

theorem native_plane_image (e : UpperHalfPlane → HyperbolicThreeSpace)
    (he : Isometry e) (A : Set UpperHalfPlane) :
    (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) (e '' A) =
      (volume : Measure UpperHalfPlane) A := by
  rw [he.euclideanHausdorffMeasure_image, native_h2_eq_volume]

theorem native_plane_transport (e : UpperHalfPlane → HyperbolicThreeSpace)
    (he : Isometry e) :
    (volume : Measure UpperHalfPlane).map e =
      (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace).restrict (range e) := by
  rw [← native_h2_eq_volume]
  exact he.map_euclideanHausdorffMeasure

#print axioms native_h2_density
#print axioms native_h2_eq_volume

end CFMPVerticalNative2Density435Transient
