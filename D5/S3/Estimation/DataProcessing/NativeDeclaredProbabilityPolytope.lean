/- GID: D5/S3/Estimation/DataProcessing/NativeDeclaredProbabilityPolytope
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/NativeDeclaredProbabilityPolytope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native finite probability laws with exact label, common source and support constraints admit finite feasible generators. -/

import D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
open D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope

noncomputable section
set_option autoImplicit false

namespace D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope

section Coordinates
variable {W : Type*} [Fintype W] [MeasurableSpace W] [MeasurableSingletonClass W]

/-- Singleton real masses on the original carrier. -/
def massVector (θ : ProbabilityMeasure W) : W → ℝ := fun w => (θ : Measure W).real {w}

lemma massVector_mem_simplex (θ : ProbabilityMeasure W) :
    massVector θ ∈ stdSimplex ℝ W := by
  refine ⟨fun _ => measureReal_nonneg, ?_⟩
  simpa [massVector, measureReal_def] using
    (sum_measureReal_singleton (μ := (θ : Measure W)) (Finset.univ : Finset W))

/-- PMF construction preserves every original carrier symbol, including zero masses. -/
def lawOfMass (x : stdSimplex ℝ W) : ProbabilityMeasure W := by
  let p : PMF W := PMF.ofFintype (fun w => ENNReal.ofReal (x.val w)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun w _ => x.property.1 w), x.property.2]
    simp)
  exact ⟨p.toMeasure, inferInstance⟩

lemma massVector_lawOfMass (x : stdSimplex ℝ W) : massVector (lawOfMass x) = x.val := by
  funext w
  simp only [massVector, lawOfMass, ProbabilityMeasure.coe_mk, measureReal_def,
    PMF.toMeasure_apply_singleton _ w (measurableSet_singleton w),
    PMF.ofFintype_apply, ENNReal.toReal_ofReal (x.property.1 w)]

lemma massVector_injective : Function.Injective (massVector (W := W)) := by
  intro θ η h
  apply ProbabilityMeasure.toMeasure_injective
  exact Measure.ext_of_measureReal_singleton (fun w => congrFun h w)

/-- The actual finite probability/simplex bijection; the inverse is explicitly PMF.toMeasure. -/
def probabilitySimplexEquiv : ProbabilityMeasure W ≃ stdSimplex ℝ W where
  toFun θ := ⟨massVector θ, massVector_mem_simplex θ⟩
  invFun := lawOfMass
  left_inv θ := massVector_injective (massVector_lawOfMass _)
  right_inv x := Subtype.ext (massVector_lawOfMass x)

lemma massVector_map {V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (f : W → V) (θ : ProbabilityMeasure W) :
    massVector (θ.map (measurable_of_countable f).aemeasurable) = pushMass f (massVector θ) := by
  classical
  funext v
  have hset : (↑(Finset.univ.filter (fun w => f w = v)) : Set W) = f ⁻¹' {v} := by
    ext w
    simp
  have hsum := sum_measureReal_singleton (μ := (θ : Measure W))
    (Finset.univ.filter (fun w => f w = v))
  rw [hset] at hsum
  change ((θ : Measure W).map f).real {v} = ∑ w, if f w = v then massVector θ w else 0
  rw [map_measureReal_apply (measurable_of_countable f) (measurableSet_singleton v)]
  simpa only [Finset.sum_filter, massVector] using hsum.symm

lemma map_eq_iff_massVector {V : Type*} [Fintype V] [MeasurableSpace V]
    [MeasurableSingletonClass V] (f : W → V)
    (θ : ProbabilityMeasure W) (Q : ProbabilityMeasure V) :
    (θ : Measure W).map f = (Q : Measure V) ↔ pushMass f (massVector θ) = massVector Q := by
  constructor
  · intro h
    have hp : θ.map (measurable_of_countable f).aemeasurable = Q := Subtype.ext h
    rw [← massVector_map f θ, hp]
  · intro h
    have hp := massVector_injective ((massVector_map f θ).trans h)
    exact congrArg ProbabilityMeasure.toMeasure hp

lemma support_one_iff_outside_zero (θ : ProbabilityMeasure W) (A : Set W) :
    (θ : Measure W) A = 1 ↔ outsideMass A (massVector θ) = 0 := by
  classical
  have hA : MeasurableSet A := (Set.toFinite A).measurableSet
  constructor
  · intro h
    have hc : (θ : Measure W) Aᶜ = 0 := by
      rw [measure_compl hA (measure_ne_top (θ : Measure W) A), measure_univ, h, tsub_self]
    funext w
    by_cases hw : w ∈ A
    · simp [outsideMass, hw]
    · have hw0 : (θ : Measure W) {w} = 0 := by
        apply le_antisymm _ bot_le
        calc
          (θ : Measure W) {w} ≤ (θ : Measure W) Aᶜ :=
            measure_mono (Set.singleton_subset_iff.mpr hw)
          _ = 0 := hc
      simp [outsideMass, hw, massVector, measureReal_def, hw0]
  · intro h
    have hsingle (w : W) (hw : w ∈ Aᶜ) : (θ : Measure W).real {w} = 0 := by
      have he := congrFun h w
      simpa [outsideMass, massVector, show w ∉ A from hw] using he
    have hcReal : (θ : Measure W).real Aᶜ = 0 := by
      have hs := sum_measureReal_singleton (μ := (θ : Measure W)) (Set.toFinite Aᶜ).toFinset
      rw [Set.Finite.coe_toFinset] at hs
      rw [← hs]
      apply Finset.sum_eq_zero
      intro w hw
      exact hsingle w ((Set.toFinite Aᶜ).mem_toFinset.mp hw)
    have hc : (θ : Measure W) Aᶜ = 0 := (measureReal_eq_zero_iff).mp hcReal
    simpa [hc] using (measure_add_measure_compl (μ := (θ : Measure W)) hA)

/-- The exact finite affine correspondence, for arbitrary real nonnegative weights.
In particular, normalized weights describe precisely the convex combinations. -/
lemma finite_mix_eq_iff {I : Type*} (S : Finset I) (a : I → ℝ)
    (η : I → ProbabilityMeasure W) (ha : ∀ i ∈ S, 0 ≤ a i)
    (θ : ProbabilityMeasure W) :
    (θ : Measure W) = ∑ i ∈ S, ENNReal.ofReal (a i) • (η i : Measure W) ↔
      massVector θ = ∑ i ∈ S, a i • massVector (η i) := by
  classical
  have hreal (w : W) :
      (∑ i ∈ S, ENNReal.ofReal (a i) • (η i : Measure W)).real {w} =
        ∑ i ∈ S, a i * massVector (η i) w := by
    rw [measureReal_def, Measure.finsetSum_apply]
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [ENNReal.toReal_sum (fun i hi =>
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (η i : Measure W) {w}))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (ha i hi)]
    rfl
  let (i : I) : IsFiniteMeasure (ENNReal.ofReal (a i) • (η i : Measure W)) :=
    Measure.smul_finite (η i : Measure W) ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (∑ i ∈ S, ENNReal.ofReal (a i) • (η i : Measure W)) :=
    inferInstance
  constructor
  · intro h
    funext w
    change (θ : Measure W).real {w} = _
    rw [h, hreal]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · intro h
    apply Measure.ext_of_measureReal_singleton
    intro w
    rw [hreal]
    have hw := congrFun h w
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, massVector] using hw

lemma native_mem_convexHull_iff (V : Finset (ProbabilityMeasure W)) (θ : ProbabilityMeasure W) :
    massVector θ ∈ convexHull ℝ (massVector '' (V : Set (ProbabilityMeasure W))) ↔
      ∃ a : ProbabilityMeasure W → ℝ, (∀ η ∈ V, 0 ≤ a η) ∧
        (∑ η ∈ V, a η) = 1 ∧
        (θ : Measure W) = ∑ η ∈ V, ENNReal.ofReal (a η) • (η : Measure W) := by
  classical
  constructor
  · intro h
    rw [← Finset.coe_image] at h
    obtain ⟨a, ha, hsum, hvec⟩ := Finset.mem_convexHull'.mp h
    have hsum' : (∑ η ∈ V, a (massVector η)) = 1 := by
      rw [Finset.sum_image] at hsum
      · exact hsum
      · intro η hη ζ hζ h
        exact massVector_injective h
    have hvec' : (∑ η ∈ V, a (massVector η) • massVector η) = massVector θ := by
      rw [Finset.sum_image] at hvec
      · exact hvec
      · intro η hη ζ hζ h
        exact massVector_injective h
    have ha' (η : ProbabilityMeasure W) (hη : η ∈ V) : 0 ≤ a (massVector η) :=
      ha _ (Finset.mem_image.mpr ⟨η, hη, rfl⟩)
    exact ⟨fun η => a (massVector η), ha', hsum',
      (finite_mix_eq_iff V _ id ha' θ).mpr hvec'.symm⟩
  · rintro ⟨a, ha, hsum, heq⟩
    have hvec := (finite_mix_eq_iff V a id ha θ).mp heq
    simp only [id_eq] at hvec
    have hh : V.centerMass a massVector ∈
        convexHull ℝ (massVector '' (V : Set (ProbabilityMeasure W))) :=
      V.centerMass_mem_convexHull ha (by rw [hsum]; exact zero_lt_one)
        (fun η hη => ⟨η, hη, rfl⟩)
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsum, ← hvec] at hh
    exact hh
end Coordinates

section NativeConstraints
variable {W Z U : Type*} [Fintype W] [Fintype Z] [Fintype U]
variable [MeasurableSpace W] [MeasurableSingletonClass W]
variable [MeasurableSpace Z] [MeasurableSingletonClass Z]
variable [MeasurableSpace U] [MeasurableSingletonClass U]

/-- Exact native class: target Q, the entire source pushforward of the same actual rho, and support. -/
def nativeFeasible (label : W → Z) (source : W → U) (A : Set W)
    (Q : ProbabilityMeasure Z) (ρ : ProbabilityMeasure W) : Set (ProbabilityMeasure W) :=
  {θ | (θ : Measure W).map label = (Q : Measure Z) ∧
    (θ : Measure W).map source = (ρ : Measure W).map source ∧ (θ : Measure W) A = 1}

lemma native_feasible_iff_coordinates (label : W → Z) (source : W → U) (A : Set W)
    (Q : ProbabilityMeasure Z) (ρ θ : ProbabilityMeasure W) :
    θ ∈ nativeFeasible label source A Q ρ ↔
      massVector θ ∈ declaredCoordinateClass label source A
        (massVector Q) (pushMass source (massVector ρ)) := by
  have hs : (θ : Measure W).map source = (ρ : Measure W).map source ↔
      pushMass source (massVector θ) = pushMass source (massVector ρ) := by
    simpa only [massVector_map, ProbabilityMeasure.toMeasure_map] using
      (map_eq_iff_massVector source θ (ρ.map (measurable_of_countable source).aemeasurable))
  simp only [nativeFeasible, declaredCoordinateClass, Set.mem_ofPred_eq,
    map_eq_iff_massVector label θ Q, hs, support_one_iff_outside_zero,
    massVector_mem_simplex, true_and]

lemma feasible_image_eq (label : W → Z) (source : W → U) (A : Set W)
    (Q : ProbabilityMeasure Z) (ρ : ProbabilityMeasure W) :
    massVector '' nativeFeasible label source A Q ρ =
      declaredCoordinateClass label source A (massVector Q) (pushMass source (massVector ρ)) := by
  ext x
  constructor
  · rintro ⟨θ, hθ, rfl⟩
    exact (native_feasible_iff_coordinates label source A Q ρ θ).mp hθ
  · intro hx
    let θ : ProbabilityMeasure W := probabilitySimplexEquiv.symm ⟨x, hx.1⟩
    have hmass : massVector θ = x :=
      congrArg Subtype.val (probabilitySimplexEquiv.apply_symm_apply ⟨x, hx.1⟩)
    refine ⟨θ, (native_feasible_iff_coordinates label source A Q ρ θ).mpr ?_, hmass⟩
    rwa [hmass]

/-- Actual finite generators are native probability laws on the untouched W carrier. -/
theorem exists_native_finite_hull (label : W → Z) (source : W → U) (A : Set W)
    (Q : ProbabilityMeasure Z) (ρ : ProbabilityMeasure W) :
    ∃ V : Finset (ProbabilityMeasure W),
      (∀ η ∈ V, η ∈ nativeFeasible label source A Q ρ) ∧
      convexHull ℝ (massVector '' (V : Set (ProbabilityMeasure W))) =
        massVector '' nativeFeasible label source A Q ρ ∧
      ∀ θ : ProbabilityMeasure W,
        θ ∈ nativeFeasible label source A Q ρ ↔
          ∃ a : ProbabilityMeasure W → ℝ, (∀ η ∈ V, 0 ≤ a η) ∧
            (∑ η ∈ V, a η) = 1 ∧
            (θ : Measure W) = ∑ η ∈ V, ENNReal.ofReal (a η) • (η : Measure W) := by
  classical
  let C := declaredCoordinateClass label source A (massVector Q) (pushMass source (massVector ρ))
  obtain ⟨T, hT⟩ := declaredCoordinateClass_isPolytope label source A
    (massVector Q) (pushMass source (massVector ρ))
  have hTC (x : T) : x.val ∈ C := by
    change x.val ∈ declaredCoordinateClass label source A
      (massVector Q) (pushMass source (massVector ρ))
    rw [← hT]
    exact subset_convexHull ℝ (T : Set (W → ℝ)) x.property
  let η : T → ProbabilityMeasure W := fun x =>
    probabilitySimplexEquiv.symm ⟨x.val, (hTC x).1⟩
  have hηmass (x : T) : massVector (η x) = x.val :=
    congrArg Subtype.val (probabilitySimplexEquiv.apply_symm_apply ⟨x.val, (hTC x).1⟩)
  let V : Finset (ProbabilityMeasure W) := Finset.univ.image η
  have hVfeas (θ : ProbabilityMeasure W) (hθ : θ ∈ V) :
      θ ∈ nativeFeasible label source A Q ρ := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hθ
    apply (native_feasible_iff_coordinates label source A Q ρ (η x)).mpr
    rw [hηmass]
    exact hTC x
  have himage : massVector '' (V : Set (ProbabilityMeasure W)) = (T : Set (W → ℝ)) := by
    ext x
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hθ
      rw [hηmass]
      exact y.property
    · intro hx
      exact ⟨η ⟨x, hx⟩, Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩,
        hηmass ⟨x, hx⟩⟩
  have hhull : convexHull ℝ (massVector '' (V : Set (ProbabilityMeasure W))) =
      massVector '' nativeFeasible label source A Q ρ := by
    rw [himage, hT, feasible_image_eq]
  refine ⟨V, hVfeas, hhull, ?_⟩
  intro θ
  rw [← native_mem_convexHull_iff, hhull]
  constructor
  · intro hθ
    exact ⟨θ, hθ, rfl⟩
  · rintro ⟨ζ, hζ, hmass⟩
    have hζθ : ζ = θ := massVector_injective hmass
    simpa only [hζθ] using hζ

end NativeConstraints
end D5.S3.Estimation.DataProcessing.NativeDeclaredProbabilityPolytope
