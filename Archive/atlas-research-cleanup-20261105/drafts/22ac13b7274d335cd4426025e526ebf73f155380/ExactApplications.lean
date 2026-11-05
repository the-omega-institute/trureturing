import D5.S3.Topology.Measures.FiniteObservationVariation
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory
open D5.S3.Topology.Measures
open NormPreservingLifts SignedRieszRepresentation FiniteObservationVariation
open D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange

universe u v w z
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [ZeroDimensionalSpace K] [MeasurableSpace K] [BorelSpace K]
variable {I : Type v} {O : I → Type w}
  [∀ i, TopologicalSpace (O i)] [∀ i, DiscreteTopology (O i)] [∀ i, Fintype (O i)]
  [∀ i, MeasurableSpace (O i)] [∀ i, BorelSpace (O i)]

-- Exact original arbitrary-family scope: no instances or hypotheses on A.
example {A : Type z} (q : ∀ i, C(K, O i))
    (hsep : Function.Injective (fun x : K => fun i => q i x))
    (s : A → SignedMeasure K)
    (hp : ∀ a, Measure.Regular (s a).toJordanDecomposition.posPart)
    (hn : ∀ a, Measure.Regular (s a).toJordanDecomposition.negPart)
    (hc : IsCompact (range (fun a => signedFunctional (s a))))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset I, ∀ a,
      (s a).totalVariation.real univ - ε <
        (SignedMeasure.totalVariation
          ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ∧
      (SignedMeasure.totalVariation
          ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ≤
        (s a).totalVariation.real univ :=
  exists_uniform_finite_readout_variation q hsep s hp hn hc ε hε

-- A continuum of distinct regular signed measures, with norm-compact functional
-- range. Riesz supplies the representatives; no unproved signed-measure norm
-- instance or scalar-functional identity is used.
example (q : ∀ i, C(K, O i))
    (hsep : Function.Injective (fun x : K => fun i => q i x))
    (x : K) :
    ∃ s : Set.Icc (0 : ℝ) 1 → SignedMeasure K,
      Function.Injective s ∧ Set.Infinite (range s) ∧
      (∀ a, (s a).toJordanDecomposition.posPart.Regular ∧
        (s a).toJordanDecomposition.negPart.Regular) ∧
      IsCompact (range (fun a => signedFunctional (s a))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ J : Finset I, ∀ a,
        (s a).totalVariation.real univ - ε <
          (SignedMeasure.totalVariation
            ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ∧
        (SignedMeasure.totalVariation
            ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ≤
          (s a).totalVariation.real univ := by
  classical
  let F : StrongDual ℝ C(K, ℝ) := ContinuousMap.evalCLM ℝ x
  have hF : F ≠ 0 := by
    intro hzero
    have heval : F (1 : C(K, ℝ)) = 1 := rfl
    rw [hzero] at heval
    norm_num at heval
  have reps (a : Set.Icc (0 : ℝ) 1) :=
    (signed_riesz_markov_kakutani (K := K)).2.2 (a.val • F)
  choose s hsreg hsF hsnorm using reps
  have hparts (a : Set.Icc (0 : ℝ) 1) :
      (s a).toJordanDecomposition.posPart.Regular ∧
      (s a).toJordanDecomposition.negPart.Regular := by
    haveI := hsreg a
    exact RegularSignedLift.regular_jordanParts_of_regular_totalVariation (s a)
  have hc : IsCompact (range (fun a => signedFunctional (s a))) := by
    simp_rw [hsF]
    exact isCompact_range (continuous_subtype_val.smul continuous_const)
  have hinj : Function.Injective s := by
    intro a b hab
    apply Subtype.ext
    apply smul_left_injective ℝ hF
    change (a : ℝ) • F = (b : ℝ) • F
    rw [← hsF a, ← hsF b, hab]
  haveI : Infinite (Set.Icc (0 : ℝ) 1) := Set.Icc.infinite (by norm_num)
  refine ⟨s, hinj, Set.infinite_range_of_injective hinj, hparts, hc, fun ε hε => ?_⟩
  exact exists_uniform_finite_readout_variation q hsep s
      (fun a => (hparts a).1) (fun a => (hparts a).2) hc ε hε

-- Empty family: compactness and Jordan regularity are discharged, not assumed.
example (q : ∀ i, C(K, O i))
    (hsep : Function.Injective (fun x : K => fun i => q i x))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset I, ∀ a : Empty,
      ((nomatch a : SignedMeasure K).totalVariation.real univ - ε <
        (SignedMeasure.totalVariation
          ((nomatch a : SignedMeasure K).map
            (finiteObservationReadout (fun i x => q i x) J))).real univ) := by
  let s : Empty → SignedMeasure K := fun a => nomatch a
  have hc : IsCompact (range (fun a => signedFunctional (s a))) := by
    have hempty : range (fun a => signedFunctional (s a)) = ∅ := by
      ext f
      constructor
      · rintro ⟨a, _⟩
        exact isEmptyElim a
      · simp
    rw [hempty]
    exact isCompact_empty
  obtain ⟨J, hJ⟩ := exists_uniform_finite_readout_variation q hsep s
    (fun a => nomatch a) (fun a => nomatch a) hc ε hε
  exact ⟨J, fun a => nomatch a⟩

-- Empty carrier: arbitrary family, compactness discharged by the singleton dual.
example [IsEmpty K] {A : Type z} (q : ∀ i, C(K, O i))
    (s : A → SignedMeasure K) (ε : ℝ) (hε : 0 < ε) :
    ∃ J : Finset I, ∀ a,
      (s a).totalVariation.real univ - ε <
        (SignedMeasure.totalVariation
          ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ∧
      (SignedMeasure.totalVariation
          ((s a).map (finiteObservationReadout (fun i x => q i x) J))).real univ ≤
        (s a).totalVariation.real univ := by
  have hc : IsCompact (range (fun a => signedFunctional (s a))) :=
    Set.Finite.isCompact (Set.toFinite _)
  apply exists_uniform_finite_readout_variation q
    (fun x => isEmptyElim x) s (fun _ => by infer_instance)
    (fun _ => by infer_instance) hc ε hε

#print axioms exists_uniform_finite_readout_variation
#print axioms NormPreservingLifts.functional_map
#print axioms RegularSignedLift.regular_add
