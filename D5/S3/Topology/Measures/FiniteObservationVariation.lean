/- GID: D5/S3/Topology/Measures/FiniteObservationVariation
   generality: G
   mirror-B: D5/B/S3/Topology/Measures/FiniteObservationVariation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite joint sensor readouts recover variation uniformly on norm-compact regular signed families. -/

import D5.S3.Topology.Measures.SignedRieszRepresentation
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
any fixed finite family, or any family with norm-compact range of signed integration functionals. The budget depends on the family
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

open NormPreservingLifts SignedRieszRepresentation

/-- Transfer the variation lost through one continuous readout between nearby
regular signed functionals. The output regularity is needed for the exact
Riesz norm identity; finite discrete readouts satisfy it automatically. -/
private theorem variation_loss_transfer
    [MeasurableSpace K] [BorelSpace K]
    {L : Type w} [TopologicalSpace L] [CompactSpace L] [T2Space L]
    [MeasurableSpace L] [BorelSpace L]
    (p : C(K, L)) (s t : SignedMeasure K)
    (hs : s.totalVariation.Regular) (ht : t.totalVariation.Regular)
    (hsp : (SignedMeasure.totalVariation (s.map p)).Regular)
    (htp : (SignedMeasure.totalVariation (t.map p)).Regular) :
    s.totalVariation.real univ - (SignedMeasure.totalVariation (s.map p)).real univ ≤
      t.totalVariation.real univ - (SignedMeasure.totalVariation (t.map p)).real univ +
        2 * ‖signedFunctional s - signedFunctional t‖ := by
  have hpull (g : C(L, ℝ)) : ‖g.comp p‖ ≤ ‖g‖ :=
    (ContinuousMap.norm_le _ (norm_nonneg _)).mpr (fun x => g.norm_coe_le_norm (p x))
  have hcontract : ‖signedFunctional (s.map p) - signedFunctional (t.map p)‖ ≤
      ‖signedFunctional s - signedFunctional t‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro g
    have h := (signedFunctional s - signedFunctional t).le_opNorm (g.comp p)
    simp only [ContinuousLinearMap.sub_apply, functional_map] at *
    exact h.trans (mul_le_mul_of_nonneg_left (hpull g) (norm_nonneg _))
  have hsource := norm_sub_norm_le (signedFunctional s) (signedFunctional t)
  have houtput := norm_sub_norm_le (signedFunctional (t.map p)) (signedFunctional (s.map p))
  rw [norm_sub_rev] at houtput
  rw [(signed_riesz_markov_kakutani (K := K)).2.1 s hs,
    (signed_riesz_markov_kakutani (K := K)).2.1 t ht,
    (signed_riesz_markov_kakutani (K := L)).2.1 (s.map p) hsp,
    (signed_riesz_markov_kakutani (K := L)).2.1 (t.map p) htp]
  linarith

/-- One finite joint sensor readout recovers variation uniformly on an
arbitrary family whose signed integration functionals have norm-compact range.
Compactness is in the StrongDual operator-norm topology, and A carries no
finiteness, countability, topology or nonemptiness requirement. -/
theorem exists_uniform_finite_readout_variation
    [ZeroDimensionalSpace K] [MeasurableSpace K] [BorelSpace K]
    [∀ i, MeasurableSpace (O i)] [∀ i, BorelSpace (O i)]
    {A : Type z}
    (q : ∀ i, C(K, O i))
    (hsep : Function.Injective (fun x : K => fun i => q i x))
    (s : A → SignedMeasure K)
    (hp : ∀ a, Measure.Regular (s a).toJordanDecomposition.posPart)
    (hn : ∀ a, Measure.Regular (s a).toJordanDecomposition.negPart)
    (hcompact : IsCompact (Set.range (fun a => signedFunctional (s a))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset I, ∀ a,
      (s a).totalVariation.real univ - ε <
        (SignedMeasure.totalVariation
          ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ∧
      (SignedMeasure.totalVariation
          ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ≤
        (s a).totalVariation.real univ := by
  classical
  have hreg (a : A) : (s a).totalVariation.Regular := by
    letI := hp a
    letI := hn a
    exact RegularSignedLift.regular_add
  obtain ⟨T, hT⟩ := hcompact.elim_finite_subcover
    (fun a => Metric.ball (signedFunctional (s a)) (ε / 4))
    (fun _ => Metric.isOpen_ball) (by
      rintro _ ⟨a, rfl⟩
      exact Set.mem_iUnion.mpr ⟨a, by simpa using (by linarith : (0 : ℝ) < ε / 4)⟩)
  obtain ⟨J, hJ⟩ := exists_common_finite_readout_variation q hsep
    (fun a : (T : Set A) => s a.val) (fun a => hp a.val) (fun a => hn a.val)
    (ε / 2) (by linarith)
  let p : C(K, FiniteObservationOutput O J) :=
    ⟨finiteObservationReadout (fun i x => q i x) J,
      continuous_pi (fun j => (q j.val).continuous)⟩
  refine ⟨J, fun a => ?_⟩
  have hmem := hT (Set.mem_range_self a)
  obtain ⟨b, hb, hab⟩ := Set.mem_iUnion₂.mp hmem
  have hdist : ‖signedFunctional (s a) - signedFunctional (s b)‖ < ε / 4 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hab
  have hloss := variation_loss_transfer p (s a) (s b) (hreg a) (hreg b)
    (by infer_instance) (by infer_instance)
  have hcenter := (hJ ⟨b, hb⟩).1
  have hcontract : (SignedMeasure.totalVariation ((s a).map p)) univ ≤
      (s a).totalVariation univ := by
    simpa only [← SignedMeasure.totalVariation_eq_variation,
      Measure.map_apply p.continuous.measurable MeasurableSet.univ, preimage_univ] using
      (VectorMeasure.variation_map_le (μ := s a) (φ := p) univ)
  exact ⟨by change (s a).totalVariation.real univ - ε <
              (SignedMeasure.totalVariation ((s a).map p)).real univ
            change (s b).totalVariation.real univ - ε / 2 <
              (SignedMeasure.totalVariation ((s b).map p)).real univ at hcenter
            linarith,
    ENNReal.toReal_mono (measure_ne_top (s a).totalVariation univ) hcontract⟩

end D5.S3.Topology.Measures.FiniteObservationVariation
