/- GID: D5/S3/Geometry/HyperbolicHausdorffDimension
   generality: G
   mirror-B: D5/B/S3/Geometry/HyperbolicHausdorffDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Measure.Hausdorff]
   utility: none
   digest: Conformal Hausdorff density in every natural dimension without local finiteness. -/

import D5.S3.Geometry.HyperbolicNormalizedDensity
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.OpenPos
import D5.S3.Geometry.HyperbolicTopology
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Tactic.GCongr

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped NNReal ENNReal
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicHausdorffComparison
open D5.S3.Geometry.HyperbolicNormalizedDensity

namespace D5.S3.Geometry.HyperbolicHausdorffDimension

private local instance : MeasurableSpace (UpperHalfSpace ℂ) := borel _
private local instance : BorelSpace (UpperHalfSpace ℂ) := ⟨rfl⟩
private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

/-- Local distortion controls Hausdorff measure in each natural dimension. -/
private theorem local_hausdorff_comparison_dim (d : ℕ) (p : UpperHalfSpace ℂ) (r : ℝ)
    (hr : 0 < r) (hrh : r < height p) (s : Set (UpperHalfSpace ℂ))
    (hs : s ⊆ Metric.ball p r) :
    Measure.hausdorffMeasure (d : ℝ) s ≤
      (ENNReal.ofReal (height p + 2*r)) ^ d *
        Measure.hausdorffMeasure (d : ℝ) (HyperbolicSpace.mk '' s) ∧
    Measure.hausdorffMeasure (d : ℝ) (HyperbolicSpace.mk '' s) ≤
      (ENNReal.ofReal ((height p-r)⁻¹)) ^ d *
        Measure.hausdorffMeasure (d : ℝ) s := by
  let K : ℝ≥0 := ⟨height p + 2*r,
    (add_pos p.property (mul_pos (by norm_num) hr)).le⟩
  let J : ℝ≥0 := ⟨(height p-r)⁻¹, inv_nonneg.mpr (sub_pos.mpr hrh).le⟩
  have forward : LipschitzOnWith J (HyperbolicSpace.mk (E := ℂ)) s := by
    apply LipschitzOnWith.of_dist_le_mul
    intro u hu v hv
    exact (ball_distortion p r hr hrh u v (hs hu) (hs hv)).2
  have backward : LipschitzOnWith K HyperbolicSpace.coordinates
      (HyperbolicSpace.mk '' s) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    exact (ball_distortion p r hr hrh u v (hs hu) (hs hv)).1
  have himage : HyperbolicSpace.coordinates '' (HyperbolicSpace.mk '' s) = s := by
    rw [← Set.image_comp]
    exact Set.image_id s
  constructor
  · have hb := backward.hausdorffMeasure_image_le (d := (d : ℝ)) (by positivity)
    simp only [ENNReal.rpow_natCast] at hb
    rw [himage] at hb
    have hK : (K : ℝ≥0∞) = ENNReal.ofReal (height p + 2*r) :=
      ENNReal.coe_nnreal_eq K
    rw [hK] at hb
    exact hb
  · have hf := forward.hausdorffMeasure_image_le (d := (d : ℝ)) (by positivity)
    simp only [ENNReal.rpow_natCast] at hf
    have hJ : (J : ℝ≥0∞) = ENNReal.ofReal ((height p-r)⁻¹) :=
      ENNReal.coe_nnreal_eq J
    rw [hJ] at hf
    exact hf

abbrev Coordinates := UpperHalfSpace ℂ
abbrev Native := HyperbolicThreeSpace

noncomputable def rawCoordinateMeasureDim (d : ℕ) : Measure Coordinates :=
  Measure.hausdorffMeasure (d : ℝ)

noncomputable def rawNativeMeasureDim (d : ℕ) : Measure Native :=
  Measure.hausdorffMeasure (d : ℝ)

noncomputable def heightDensityDim (d : ℕ) (x : Coordinates) : ℝ≥0∞ :=
  ENNReal.ofReal ((height x)⁻¹ ^ d)

-- Local Hausdorff distortion compares the pushed-forward native measure.
variable {d : ℕ}

private theorem raw_coordinate_local_comparison
    (p : Coordinates) (r : ℝ) (hr : 0 < r) (hrh : r < height p)
    (s : Set Coordinates) (hs : MeasurableSet s)
    (hsp : s ⊆ Metric.ball p r) :
    rawCoordinateMeasureDim d s ≤
        (ENNReal.ofReal (height p + 2 * r)) ^ d *
          ((rawNativeMeasureDim d).map coordinatesEquiv) s ∧
      ((rawNativeMeasureDim d).map coordinatesEquiv) s ≤
        (ENNReal.ofReal ((height p - r)⁻¹)) ^ d *
          rawCoordinateMeasureDim d s := by
  have h := local_hausdorff_comparison_dim d p r hr hrh s hsp
  have hmap : ((rawNativeMeasureDim d).map coordinatesEquiv) s =
      rawNativeMeasureDim d (HyperbolicSpace.mk '' s) := by
    rw [Measure.map_apply coordinatesEquiv.measurable hs]
    congr 1
    exact congrFun (Set.image_eq_preimage_of_inverse
      (f := HyperbolicSpace.mk (E := ℂ)) (g := coordinatesEquiv)
      (fun x : Coordinates => rfl) (fun x : Native => rfl)).symm s
  rw [hmap]
  exact h

private def distortionFactorDim (d : ℕ) (ε : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + 2 * ε) / (1 - ε)) ^ d)

private theorem local_density_sandwich
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (p : Coordinates) (s : Set Coordinates) (hs : MeasurableSet s)
    (hsp : s ⊆ Metric.ball p (ε * height p)) :
    (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) s ≤
        distortionFactorDim d ε * ((rawNativeMeasureDim d).map coordinatesEquiv) s ∧
      ((rawNativeMeasureDim d).map coordinatesEquiv) s ≤
        distortionFactorDim d ε * (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) s := by
  let r := ε * height p
  have hp : 0 < height p := p.property
  have hr : 0 < r := mul_pos hε0 hp
  have hrh : r < height p := by dsimp [r]; nlinarith
  have hl : 0 < height p - r := sub_pos.mpr hrh
  have hg : 0 < height p + 2 * r := by positivity
  let α : ℝ≥0∞ := ENNReal.ofReal ((height p - r)⁻¹) ^ d
  let γ : ℝ≥0∞ := ENNReal.ofReal (height p + 2 * r) ^ d
  have hh (x : Coordinates) (hx : x ∈ s) :
      height p - r ≤ height x ∧ height x ≤ height p + 2 * r := by
    have hd : |height x - height p| ≤ dist x p := WithLp.dist_snd_le x.val p.val
    have hxball : dist x p < r := hsp hx
    have ha := abs_le.mp (hd.trans hxball.le)
    constructor <;> linarith
  have hu (x : Coordinates) (hx : x ∈ s) : heightDensityDim d x ≤ α := by
    dsimp [heightDensityDim, α]
    rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hl.le)]
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (inv_nonneg.mpr x.property.le)
      (inv_anti₀ hl (hh x hx).1) d
  have hγ0 : γ ≠ 0 := by dsimp [γ]; positivity
  have hγtop : γ ≠ ∞ := by dsimp [γ]; finiteness
  have hdlo (x : Coordinates) (hx : x ∈ s) : γ⁻¹ ≤ heightDensityDim d x := by
    dsimp [γ, heightDensityDim]
    rw [ENNReal.inv_pow, ← ENNReal.ofReal_inv_of_pos hg,
      ← ENNReal.ofReal_pow (inv_nonneg.mpr hg.le)]
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (inv_nonneg.mpr hg.le)
      (inv_anti₀ x.property (hh x hx).2) d
  have hηupper : (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) s ≤ α * rawCoordinateMeasureDim d s := by
    rw [withDensity_apply (heightDensityDim d) hs]
    calc
      _ ≤ ∫⁻ x in s, α ∂rawCoordinateMeasureDim d := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hs] with x hx
        exact hu x hx
      _ = _ := by simp
  have hηlower : γ⁻¹ * rawCoordinateMeasureDim d s ≤ (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) s := by
    rw [withDensity_apply (heightDensityDim d) hs]
    calc
      _ = ∫⁻ x in s, γ⁻¹ ∂rawCoordinateMeasureDim d := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hs] with x hx
        exact hdlo x hx
  have hηreverse : rawCoordinateMeasureDim d s ≤ γ * (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) s := by
    have : γ * (γ⁻¹ * rawCoordinateMeasureDim d s) ≤
        γ * (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) s := by gcongr
    simpa only [← mul_assoc, ENNReal.mul_inv_cancel hγ0 hγtop, one_mul] using this
  have hn := raw_coordinate_local_comparison (d := d) p r hr hrh s hs hsp
  have hfactor : α * γ = distortionFactorDim d ε := by
    dsimp [α, γ, distortionFactorDim]
    rw [← mul_pow, ← ENNReal.ofReal_mul (inv_nonneg.mpr hl.le),
      ← ENNReal.ofReal_pow (by positivity)]
    congr 2
    dsimp [r]
    field_simp
  constructor
  · calc
      _ ≤ α * rawCoordinateMeasureDim d s := hηupper
      _ ≤ α * (γ * ((rawNativeMeasureDim d).map coordinatesEquiv) s) := by gcongr; exact hn.1
      _ = _ := by rw [← mul_assoc, hfactor]
  · calc
      _ ≤ α * rawCoordinateMeasureDim d s := hn.2
      _ ≤ α * (γ * (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) s) := by gcongr
      _ = _ := by rw [← mul_assoc, hfactor]

private theorem global_density_sandwich
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (s : Set Coordinates) (hs : MeasurableSet s) :
    (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) s ≤
        distortionFactorDim d ε * ((rawNativeMeasureDim d).map coordinatesEquiv) s ∧
      ((rawNativeMeasureDim d).map coordinatesEquiv) s ≤
        distortionFactorDim d ε * (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) s := by
  let V : Coordinates → Set Coordinates := fun p => Metric.ball p (ε * height p)
  let : Nonempty Coordinates := ⟨⟨WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)), by norm_num⟩⟩
  have hVcover : (Set.univ : Set Coordinates) ⊆ ⋃ p, V p := by
    intro x _
    apply Set.mem_iUnion.mpr
    refine ⟨x, ?_⟩
    simpa only [V, Metric.mem_ball, dist_self] using
      mul_pos hε0 (show 0 < height x from x.property)
  obtain ⟨z, hz⟩ := IsLindelof.indexed_countable_subcover
    (isLindelof_univ : IsLindelof (Set.univ : Set Coordinates)) V (fun _ => Metric.isOpen_ball) hVcover
  have hzcover : (⋃ n, V (z n)) = Set.univ := Set.Subset.antisymm (Set.subset_univ _) hz
  let D : ℕ → Set Coordinates := disjointed (fun n => V (z n))
  have hDm : ∀ n, MeasurableSet (D n) :=
    MeasurableSet.disjointed (fun n => (Metric.isOpen_ball : IsOpen (V (z n))).measurableSet)
  have hDsub : ∀ n, D n ⊆ V (z n) := fun n => disjointed_subset _ n
  have hDdisj : Pairwise (fun i j => Disjoint (D i) (D j)) := disjoint_disjointed _
  have hDcover : (⋃ n, D n) = Set.univ := by
    dsimp [D]
    rw [iUnion_disjointed, hzcover]
  have hPm : ∀ n, MeasurableSet (s ∩ D n) := fun n => hs.inter (hDm n)
  have hPdisj : Pairwise (fun i j => Disjoint (s ∩ D i) (s ∩ D j)) :=
    fun i j hij => (hDdisj hij).mono inter_subset_right inter_subset_right
  have hPcover : (⋃ n, s ∩ D n) = s := by
    rw [← Set.inter_iUnion, hDcover, Set.inter_univ]
  have hsum (ρ : Measure Coordinates) : ρ s = ∑' n, ρ (s ∩ D n) := by
    rw [← measure_iUnion hPdisj hPm, hPcover]
  have hlocal (n : ℕ) := local_density_sandwich (d := d) ε hε0 hε1 (z n) (s ∩ D n)
    (hPm n) (inter_subset_right.trans (hDsub n))
  constructor
  · calc
      _ = ∑' n, (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) (s ∩ D n) := hsum _
      _ ≤ ∑' n, distortionFactorDim d ε * ((rawNativeMeasureDim d).map coordinatesEquiv) (s ∩ D n) :=
        ENNReal.tsum_le_tsum fun n => (hlocal n).1
      _ = distortionFactorDim d ε * ∑' n, ((rawNativeMeasureDim d).map coordinatesEquiv) (s ∩ D n) :=
        ENNReal.tsum_mul_left
      _ = _ := by rw [← hsum]
  · calc
      _ = ∑' n, ((rawNativeMeasureDim d).map coordinatesEquiv) (s ∩ D n) := hsum _
      _ ≤ ∑' n, distortionFactorDim d ε * (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) (s ∩ D n) :=
        ENNReal.tsum_le_tsum fun n => (hlocal n).2
      _ = distortionFactorDim d ε * ∑' n, (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) (s ∩ D n) :=
        ENNReal.tsum_mul_left
      _ = _ := by rw [← hsum]

/-- Native Hausdorff measure in every natural dimension has the conformal height density.
No local finiteness of the Hausdorff measure is assumed. -/
theorem raw_native_density_nat (d : ℕ) :
    (rawNativeMeasureDim d).map coordinatesEquiv =
      (rawCoordinateMeasureDim d).withDensity (heightDensityDim d) := by
  apply Measure.ext
  intro s hs
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1 + 1)
  have hε0 (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hε1 (n : ℕ) : ε n < 1 := by
    dsimp [ε]
    apply (div_lt_one (by positivity)).2
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hε : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    simpa [ε, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
        (Filter.tendsto_add_atTop_nat 1)
  have hk : Filter.Tendsto (fun n => distortionFactorDim d (ε n)) Filter.atTop (nhds 1) := by
    have hh : Filter.Tendsto (fun n => ((1 + 2 * ε n) / (1 - ε n)) ^ d)
        Filter.atTop (nhds (((1 + 2 * 0) / (1 - 0) : ℝ) ^ d)) :=
      ((tendsto_const_nhds.add (tendsto_const_nhds.mul hε)).div
      (tendsto_const_nhds.sub hε) (by norm_num : (1 : ℝ) - 0 ≠ 0)).pow d
    simpa [distortionFactorDim, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have hlim (b : ℝ≥0∞) :
      Filter.Tendsto (fun n => distortionFactorDim d (ε n) * b) Filter.atTop (nhds b) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hk (Or.inl (by simp : (1 : ℝ≥0∞) ≠ 0))
  apply le_antisymm
  · exact ge_of_tendsto' (hlim _) fun n => (global_density_sandwich (d := d) (ε n) (hε0 n) (hε1 n) s hs).2
  · exact ge_of_tendsto' (hlim _) fun n => (global_density_sandwich (d := d) (ε n) (hε0 n) (hε1 n) s hs).1

end D5.S3.Geometry.HyperbolicHausdorffDimension
