import D5.S3.Topology.Measures.FiniteObservationVariation

open Set MeasureTheory
open D5.S3.Topology.Measures.FiniteObservationVariation
open D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange

universe u v w z

-- Exact application to a finite family of pairwise signed discrepancies.
example {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [ZeroDimensionalSpace K] [MeasurableSpace K] [BorelSpace K]
    {I : Type v} {O : I → Type w}
    [∀ i, TopologicalSpace (O i)] [∀ i, DiscreteTopology (O i)]
    [∀ i, Fintype (O i)] [∀ i, MeasurableSpace (O i)] [∀ i, BorelSpace (O i)]
    {A : Type z} [Fintype A]
    (q : ∀ i, C(K, O i))
    (hsep : Function.Injective (fun x : K => fun i => q i x))
    (s : A → SignedMeasure K)
    (hp : ∀ a b, Measure.Regular (s a - s b).toJordanDecomposition.posPart)
    (hn : ∀ a b, Measure.Regular (s a - s b).toJordanDecomposition.negPart)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset I, ∀ a b,
      (s a - s b).totalVariation.real univ - ε <
        (SignedMeasure.totalVariation
          ((s a).map (finiteObservationReadout (fun i x => q i x) J) -
            (s b).map (finiteObservationReadout (fun i x => q i x) J))).real univ ∧
      (SignedMeasure.totalVariation
          ((s a).map (finiteObservationReadout (fun i x => q i x) J) -
            (s b).map (finiteObservationReadout (fun i x => q i x) J))).real univ ≤
        (s a - s b).totalVariation.real univ := by
  obtain ⟨J, hJ⟩ := exists_common_finite_readout_variation q hsep
    (fun ab : A × A => s ab.1 - s ab.2)
    (fun ab => hp ab.1 ab.2) (fun ab => hn ab.1 ab.2) ε hε
  refine ⟨J, fun a b => ?_⟩
  have h := hJ (a, b)
  have heq : (s a - s b).map (finiteObservationReadout (fun i x => q i x) J) =
      (s a).map (finiteObservationReadout (fun i x => q i x) J) -
      (s b).map (finiteObservationReadout (fun i x => q i x) J) :=
    map_sub (VectorMeasure.mapGm _) (s a) (s b)
  simpa only [heq] using h

#print axioms D5.S3.Topology.Measures.FiniteObservationVariation.exists_common_finite_readout_variation
