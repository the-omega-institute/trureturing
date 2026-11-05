/- GID: D5/S3/Topology/Measures/FiniteObservationVariation
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/FiniteObservationVariation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One finite joint sensor readout approximates a finite signed family's variation masses. -/

import D5.S3.Topology.Measures.PositiveClopenMass
import D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Topology.Category.Profinite.Product
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Data.Fintype.EquivFin

/-!
# Variation recovered by finite joint observations

A point-separating family of continuous finite discrete sensors on a compact
zero-dimensional Hausdorff Borel space detects the whole variation mass of
each regular signed measure to arbitrary accuracy. One budget suffices for
any fixed finite family of signed measures. The budget depends on the family
and the accuracy; no bound uniform over measures or accuracies is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory

namespace D5.S3.Topology.Measures.FiniteObservationVariation

open D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange

universe u v w z

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
variable {I : Type v} {O : I → Type w}
variable [∀ i, TopologicalSpace (O i)] [∀ i, DiscreteTopology (O i)]
variable [∀ i, Fintype (O i)]

/-- Compact profinite descent, used for each clopen Jordan near-maximizer. -/
private lemma exists_finite_support (q : ∀ i, C(K, O i))
    (hsep : Function.Injective (fun x : K => fun i => q i x))
    {A : Set K} (hA : IsClopen A) :
    ∃ J : Finset I, ∀ x y, (∀ i ∈ J, q i x = q i y) → (x ∈ A ↔ y ∈ A) := by
  classical
  let code (i : I) : O i ≃ Fin (Fintype.card (O i)) := Fintype.equivFin (O i)
  let c : K → (∀ i, Fin (Fintype.card (O i))) := fun x i => code i (q i x)
  have hc : Continuous c := continuous_pi (fun i =>
    continuous_of_discreteTopology.comp (q i).continuous)
  have hinj : Function.Injective c := by
    intro x y hxy
    apply hsep
    funext i
    exact (code i).injective (congrFun hxy i)
  let e : K ≃ₜ Set.range c := (hc.isClosedEmbedding hinj).isEmbedding.toHomeomorph
  have hC : IsCompact (Set.range c) := isCompact_range hc
  let U : Set (Set.range c) := e.symm ⁻¹' A
  obtain ⟨J, V, _, hU⟩ := Profinite.exists_isClopen_of_cofiltered
    (Profinite.indexCone hC) (Profinite.indexCone_isLimit hC)
    (show IsClopen U from hA.preimage e.symm.continuous)
  refine ⟨Opposite.unop J, ?_⟩
  intro x y hxy
  have hpi : Profinite.IndexFunctor.π_app (Set.range c) (· ∈ Opposite.unop J) (e x) =
      Profinite.IndexFunctor.π_app (Set.range c) (· ∈ Opposite.unop J) (e y) := by
    apply Subtype.ext
    funext i
    exact congrArg (code i.val) (hxy i.val i.property)
  have hmem : e x ∈ U ↔ e y ∈ U := by
    rw [hU]
    exact iff_of_eq (congrArg (fun a => a ∈ V) hpi)
  simpa only [U, mem_preimage, e.symm_apply_apply] using hmem

/-- A single finite joint readout retains, within any prescribed positive
accuracy, the total-variation mass of every member of a fixed finite family.
Both Jordan parts are explicitly regular. No finite readout is assumed
injective or norm preserving. Empty carriers and empty families are allowed. -/
theorem exists_common_finite_readout_variation
    [ZeroDimensionalSpace K] [MeasurableSpace K] [BorelSpace K]
    [∀ i, MeasurableSpace (O i)] [∀ i, BorelSpace (O i)]
    {A : Type z} [Fintype A]
    (q : ∀ i, C(K, O i))
    (hsep : Function.Injective (fun x : K => fun i => q i x))
    (s : A → SignedMeasure K)
    (hp : ∀ a, Measure.Regular (s a).toJordanDecomposition.posPart)
    (hn : ∀ a, Measure.Regular (s a).toJordanDecomposition.negPart)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset I, ∀ a,
      (s a).totalVariation.real univ - ε <
        (SignedMeasure.totalVariation
          ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ∧
      (SignedMeasure.totalVariation
          ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ≤
        (s a).totalVariation.real univ := by
  classical
  have hnear (a : A) : ∃ W : Set K, IsClopen W ∧ W ⊆ univ ∧
      (s a).toJordanDecomposition.posPart.real univ - ε / 2 < (s a) W := by
    apply PositiveClopenMass.exists_isClopen_subset_lt_apply_of_lt_posPart
      (s a) (hp a) (hn a) isOpen_univ
    linarith
  choose W hW hWsub hWnear using hnear
  choose D hD using fun a => exists_finite_support q hsep (hW a)
  let J : Finset I := Finset.univ.biUnion D
  let p := finiteObservationReadout (fun i x => q i x) J
  have hpc : Continuous p := continuous_pi (fun j => (q j.val).continuous)
  have hpm : Measurable p := hpc.measurable
  refine ⟨J, fun a => ?_⟩
  let B : Set (FiniteObservationOutput O J) := p '' W a
  have hB : MeasurableSet B := (isClopen_discrete B).isOpen.measurableSet
  have hpre : p ⁻¹' B = W a := by
    ext x
    constructor
    · rintro ⟨y, hy, hyx⟩
      apply (hD a y x (fun i hi => ?_)).mp hy
      have hiJ : i ∈ J := Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hi⟩
      exact congrFun hyx ⟨i, hiJ⟩
    · intro hx
      exact ⟨x, hx, rfl⟩
  have heval : (s a).map p B = (s a) (W a) := by
    rw [VectorMeasure.map_apply (s a) hpm hB, hpre]
  have hpos : (s a).toJordanDecomposition.posPart.real univ - ε / 2 <
      (SignedMeasure.toJordanDecomposition ((s a).map p)).posPart.real univ := by
    have hmono := measureReal_mono
      (μ := (SignedMeasure.toJordanDecomposition ((s a).map p)).posPart) (subset_univ B)
    have hneg : 0 ≤
        (SignedMeasure.toJordanDecomposition ((s a).map p)).negPart.real B :=
      measureReal_nonneg
    have hj := SignedMeasure.apply_eq_posPart_real_sub_negPart_real ((s a).map p) hB
    linarith [hWnear a]
  have hmass : (s a).map p univ = (s a) univ := by
    rw [VectorMeasure.map_apply (s a) hpm MeasurableSet.univ, preimage_univ]
  have hs := (s a).apply_eq_posPart_real_sub_negPart_real MeasurableSet.univ
  have ht := SignedMeasure.apply_eq_posPart_real_sub_negPart_real ((s a).map p)
    MeasurableSet.univ
  have hvs : (s a).totalVariation.real univ =
      (s a).toJordanDecomposition.posPart.real univ +
        (s a).toJordanDecomposition.negPart.real univ := measureReal_add_apply
  have hvt : (SignedMeasure.totalVariation ((s a).map p)).real univ =
      (SignedMeasure.toJordanDecomposition ((s a).map p)).posPart.real univ +
        (SignedMeasure.toJordanDecomposition ((s a).map p)).negPart.real univ :=
    measureReal_add_apply
  have hcontract : (SignedMeasure.totalVariation ((s a).map p)) univ ≤
      (s a).totalVariation univ := by
    simpa only [← SignedMeasure.totalVariation_eq_variation,
      Measure.map_apply hpm MeasurableSet.univ, preimage_univ] using
      (VectorMeasure.variation_map_le (μ := s a) (φ := p) univ)
  exact ⟨by change (s a).totalVariation.real univ - ε <
              (SignedMeasure.totalVariation ((s a).map p)).real univ
            linarith,
    ENNReal.toReal_mono (measure_ne_top (s a).totalVariation univ) hcontract⟩

end D5.S3.Topology.Measures.FiniteObservationVariation
