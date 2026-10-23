/- GID: D5/S3/Geometry/HyperbolicNormalizedDensity
   generality: G
   mirror-B: D5/B/S3/Geometry/HyperbolicNormalizedDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Measure.Hausdorff]
   utility: none
   digest: Raw native Hausdorff density from local distortion, countable additivity and squeeze. -/

import D5.S3.Geometry.HyperbolicHausdorffComparison
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

namespace D5.S3.Geometry.HyperbolicNormalizedDensity

private local instance : MeasurableSpace (UpperHalfSpace ℂ) := borel _
private local instance : BorelSpace (UpperHalfSpace ℂ) := ⟨rfl⟩
private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

abbrev Coordinates3 := UpperHalfSpace ℂ
abbrev Native3 := HyperbolicThreeSpace

noncomputable def coordinatesEquiv : Native3 ≃ᵐ Coordinates3 :=
  (D5.S3.Geometry.HyperbolicTopology.coordinatesHomeomorph (E := ℂ)).toMeasurableEquiv

noncomputable def rawCoordinateMeasure : Measure Coordinates3 :=
  Measure.hausdorffMeasure 3

noncomputable def rawNativeMeasure : Measure Native3 :=
  Measure.hausdorffMeasure 3

noncomputable def heightDensity (x : Coordinates3) : ℝ≥0∞ :=
  ENNReal.ofReal ((height x)⁻¹ ^ (3 : ℕ))

private theorem coordinatesEquiv_preimage (s : Set Coordinates3) :
    coordinatesEquiv ⁻¹' s = HyperbolicSpace.mk '' s := by
  ext z
  constructor
  · intro hz
    change z.coordinates ∈ s at hz
    exact ⟨z.coordinates, hz, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    change x ∈ s
    exact hx

/-- Local Hausdorff distortion gives a comparison for the pushed-forward native measure. -/
private theorem raw_coordinate_local_comparison
    (p : Coordinates3) (r : ℝ) (hr : 0 < r) (hrh : r < height p)
    (s : Set Coordinates3) (hs : MeasurableSet s)
    (hsp : s ⊆ Metric.ball p r) :
    rawCoordinateMeasure s ≤
        (ENNReal.ofReal (height p + 2 * r)) ^ (3 : ℝ) *
          (rawNativeMeasure.map coordinatesEquiv) s ∧
      (rawNativeMeasure.map coordinatesEquiv) s ≤
        (ENNReal.ofReal ((height p - r)⁻¹)) ^ (3 : ℝ) *
          rawCoordinateMeasure s := by
  have h := local_hausdorff_comparison p r hr hrh s hsp
  have hmap : (rawNativeMeasure.map coordinatesEquiv) s =
      rawNativeMeasure (HyperbolicSpace.mk '' s) := by
    rw [Measure.map_apply coordinatesEquiv.measurable hs]
    rw [coordinatesEquiv_preimage]
  rw [hmap]
  exact h

private def distortionFactor (ε : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + 2 * ε) / (1 - ε)) ^ (3 : ℕ))

private theorem local_density_sandwich
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (p : Coordinates3) (s : Set Coordinates3) (hs : MeasurableSet s)
    (hsp : s ⊆ Metric.ball p (ε * height p)) :
    rawCoordinateMeasure.withDensity heightDensity s ≤
        distortionFactor ε * (rawNativeMeasure.map coordinatesEquiv) s ∧
      (rawNativeMeasure.map coordinatesEquiv) s ≤
        distortionFactor ε * rawCoordinateMeasure.withDensity heightDensity s := by
  let r := ε * height p
  have hp : 0 < height p := p.property
  have hr : 0 < r := mul_pos hε0 hp
  have hrh : r < height p := by dsimp [r]; nlinarith
  have hl : 0 < height p - r := sub_pos.mpr hrh
  have hg : 0 < height p + 2 * r := by positivity
  let α : ℝ≥0∞ := ENNReal.ofReal ((height p - r)⁻¹) ^ (3 : ℕ)
  let γ : ℝ≥0∞ := ENNReal.ofReal (height p + 2 * r) ^ (3 : ℕ)
  have hh (x : Coordinates3) (hx : x ∈ s) :
      height p - r ≤ height x ∧ height x ≤ height p + 2 * r := by
    have hd : |height x - height p| ≤ dist x p := WithLp.dist_snd_le x.val p.val
    have hxball : dist x p < r := hsp hx
    have ha := abs_le.mp (hd.trans hxball.le)
    constructor <;> linarith
  have hu (x : Coordinates3) (hx : x ∈ s) : heightDensity x ≤ α := by
    dsimp [heightDensity, α]
    rw [← ENNReal.ofReal_pow (inv_nonneg.mpr hl.le)]
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (inv_nonneg.mpr x.property.le)
      (inv_anti₀ hl (hh x hx).1) 3
  have hγ0 : γ ≠ 0 := by dsimp [γ]; positivity
  have hγtop : γ ≠ ∞ := by dsimp [γ]; finiteness
  have hdlo (x : Coordinates3) (hx : x ∈ s) : γ⁻¹ ≤ heightDensity x := by
    dsimp [γ, heightDensity]
    rw [ENNReal.inv_pow, ← ENNReal.ofReal_inv_of_pos hg,
      ← ENNReal.ofReal_pow (inv_nonneg.mpr hg.le)]
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (inv_nonneg.mpr hg.le)
      (inv_anti₀ x.property (hh x hx).2) 3
  have hηupper : rawCoordinateMeasure.withDensity heightDensity s ≤ α * rawCoordinateMeasure s := by
    rw [withDensity_apply heightDensity hs]
    calc
      _ ≤ ∫⁻ x in s, α ∂rawCoordinateMeasure := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hs] with x hx
        exact hu x hx
      _ = _ := by simp
  have hηlower : γ⁻¹ * rawCoordinateMeasure s ≤ rawCoordinateMeasure.withDensity heightDensity s := by
    rw [withDensity_apply heightDensity hs]
    calc
      _ = ∫⁻ x in s, γ⁻¹ ∂rawCoordinateMeasure := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hs] with x hx
        exact hdlo x hx
  have hηreverse : rawCoordinateMeasure s ≤ γ * rawCoordinateMeasure.withDensity heightDensity s := by
    have : γ * (γ⁻¹ * rawCoordinateMeasure s) ≤
        γ * rawCoordinateMeasure.withDensity heightDensity s := by gcongr
    simpa only [← mul_assoc, ENNReal.mul_inv_cancel hγ0 hγtop, one_mul] using this
  have hn := raw_coordinate_local_comparison p r hr hrh s hs hsp
  have hpowers : (3 : ℝ) = ((3 : ℕ) : ℝ) := rfl
  simp only [hpowers, ENNReal.rpow_natCast] at hn
  have hfactor : α * γ = distortionFactor ε := by
    dsimp [α, γ, distortionFactor]
    rw [← mul_pow, ← ENNReal.ofReal_mul (inv_nonneg.mpr hl.le),
      ← ENNReal.ofReal_pow (by positivity)]
    congr 2
    dsimp [r]
    field_simp
  constructor
  · calc
      _ ≤ α * rawCoordinateMeasure s := hηupper
      _ ≤ α * (γ * (rawNativeMeasure.map coordinatesEquiv) s) := by gcongr; exact hn.1
      _ = _ := by rw [← mul_assoc, hfactor]
  · calc
      _ ≤ α * rawCoordinateMeasure s := hn.2
      _ ≤ α * (γ * rawCoordinateMeasure.withDensity heightDensity s) := by gcongr
      _ = _ := by rw [← mul_assoc, hfactor]

private theorem global_density_sandwich
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (s : Set Coordinates3) (hs : MeasurableSet s) :
    rawCoordinateMeasure.withDensity heightDensity s ≤
        distortionFactor ε * (rawNativeMeasure.map coordinatesEquiv) s ∧
      (rawNativeMeasure.map coordinatesEquiv) s ≤
        distortionFactor ε * rawCoordinateMeasure.withDensity heightDensity s := by
  let V : Coordinates3 → Set Coordinates3 := fun p => Metric.ball p (ε * height p)
  let : Nonempty Coordinates3 := ⟨⟨WithLp.toLp 2 ((0 : ℂ), (1 : ℝ)), by norm_num⟩⟩
  have hVcover : (Set.univ : Set Coordinates3) ⊆ ⋃ p, V p := by
    intro x _
    apply Set.mem_iUnion.mpr
    refine ⟨x, ?_⟩
    simpa only [V, Metric.mem_ball, dist_self] using
      mul_pos hε0 (show 0 < height x from x.property)
  obtain ⟨z, hz⟩ := IsLindelof.indexed_countable_subcover
    (isLindelof_univ : IsLindelof (Set.univ : Set Coordinates3)) V (fun _ => Metric.isOpen_ball) hVcover
  have hzcover : (⋃ n, V (z n)) = Set.univ := Set.Subset.antisymm (Set.subset_univ _) hz
  let D : ℕ → Set Coordinates3 := disjointed (fun n => V (z n))
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
  have hsum (ρ : Measure Coordinates3) : ρ s = ∑' n, ρ (s ∩ D n) := by
    rw [← measure_iUnion hPdisj hPm, hPcover]
  have hlocal (n : ℕ) := local_density_sandwich ε hε0 hε1 (z n) (s ∩ D n)
    (hPm n) (inter_subset_right.trans (hDsub n))
  constructor
  · calc
      _ = ∑' n, rawCoordinateMeasure.withDensity heightDensity (s ∩ D n) := hsum _
      _ ≤ ∑' n, distortionFactor ε * (rawNativeMeasure.map coordinatesEquiv) (s ∩ D n) :=
        ENNReal.tsum_le_tsum fun n => (hlocal n).1
      _ = distortionFactor ε * ∑' n, (rawNativeMeasure.map coordinatesEquiv) (s ∩ D n) :=
        ENNReal.tsum_mul_left
      _ = _ := by rw [← hsum]
  · calc
      _ = ∑' n, (rawNativeMeasure.map coordinatesEquiv) (s ∩ D n) := hsum _
      _ ≤ ∑' n, distortionFactor ε * rawCoordinateMeasure.withDensity heightDensity (s ∩ D n) :=
        ENNReal.tsum_le_tsum fun n => (hlocal n).2
      _ = distortionFactor ε * ∑' n, rawCoordinateMeasure.withDensity heightDensity (s ∩ D n) :=
        ENNReal.tsum_mul_left
      _ = _ := by rw [← hsum]

/-- Original native Hausdorff three-measure in the original coordinates equals
Euclidean-coordinate raw Hausdorff three-measure with density height⁻³.
This is an equality of measures, with no finiteness or density-identity premise. -/
theorem raw_native_density :
    rawNativeMeasure.map coordinatesEquiv =
      rawCoordinateMeasure.withDensity heightDensity := by
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
  have hk : Filter.Tendsto (fun n => distortionFactor (ε n)) Filter.atTop (nhds 1) := by
    have hh : Filter.Tendsto (fun n => ((1 + 2 * ε n) / (1 - ε n)) ^ 3)
        Filter.atTop (nhds (((1 + 2 * 0) / (1 - 0) : ℝ) ^ 3)) :=
      ((tendsto_const_nhds.add (tendsto_const_nhds.mul hε)).div
      (tendsto_const_nhds.sub hε) (by norm_num : (1 : ℝ) - 0 ≠ 0)).pow 3
    simpa [distortionFactor, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hh
  have hlim (b : ℝ≥0∞) :
      Filter.Tendsto (fun n => distortionFactor (ε n) * b) Filter.atTop (nhds b) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hk (Or.inl (by simp : (1 : ℝ≥0∞) ≠ 0))
  apply le_antisymm
  · exact ge_of_tendsto' (hlim _) fun n => (global_density_sandwich (ε n) (hε0 n) (hε1 n) s hs).2
  · exact ge_of_tendsto' (hlim _) fun n => (global_density_sandwich (ε n) (hε0 n) (hε1 n) s hs).1


end D5.S3.Geometry.HyperbolicNormalizedDensity
