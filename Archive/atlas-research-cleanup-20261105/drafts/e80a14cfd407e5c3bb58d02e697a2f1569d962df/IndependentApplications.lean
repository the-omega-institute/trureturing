import D5.S3.Topology.Measures.FiniteObservationVariation
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set MeasureTheory
open D5.S3.Topology.Measures
open NormPreservingLifts SignedRieszRepresentation FiniteObservationVariation
open D5.S3.ConceptDynamics.CanonicalImage.FiniteObservationQuotientRange

universe u v w z

-- Check the full original telescope and literal finite joint readout.
theorem review_exact_statement
    {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [ZeroDimensionalSpace K] [MeasurableSpace K] [BorelSpace K]
    {I : Type v} {O : I → Type w}
    [∀ i, TopologicalSpace (O i)] [∀ i, DiscreteTopology (O i)] [∀ i, Fintype (O i)]
    [∀ i, MeasurableSpace (O i)] [∀ i, BorelSpace (O i)]
    {A : Type z} (q : ∀ i, C(K, O i))
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

-- Independently discharge every compact-family hypothesis on Cantor space.
-- The interval contains negative and positive coefficients and infinitely many
-- distinct regular signed representatives. No finite carrier/readout injection
-- is supplied to the recovery theorem. Check both directions as a loss bound.
theorem review_cantor_signed_interval :
    let K := ℕ → Bool
    letI : MeasurableSpace K := borel K
    letI : BorelSpace K := ⟨rfl⟩
    ∃ s : Set.Icc (-1 : ℝ) 1 → SignedMeasure K,
      Function.Injective s ∧ Set.Infinite (range s) ∧
      (∀ a, (s a).toJordanDecomposition.posPart.Regular ∧
        (s a).toJordanDecomposition.negPart.Regular) ∧
      IsCompact (range (fun a => signedFunctional (s a))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ J : Finset ℕ, ∀ a,
        0 ≤ (s a).totalVariation.real univ -
          (SignedMeasure.totalVariation
            ((s a).map (finiteObservationReadout (fun i (x : K) => x i) J))).real univ ∧
        (s a).totalVariation.real univ -
          (SignedMeasure.totalVariation
            ((s a).map (finiteObservationReadout (fun i (x : K) => x i) J))).real univ < ε := by
  classical
  dsimp only
  let K := ℕ → Bool
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  let x : K := fun _ => false
  let F : StrongDual ℝ C(K, ℝ) := ContinuousMap.evalCLM ℝ x
  have hF : F ≠ 0 := by
    intro hzero
    have heval : F (1 : C(K, ℝ)) = 1 := rfl
    rw [hzero] at heval
    norm_num at heval
  have reps (a : Set.Icc (-1 : ℝ) 1) :=
    (signed_riesz_markov_kakutani (K := K)).2.2 (a.val • F)
  choose s hsreg hsF hsnorm using reps
  have hparts (a : Set.Icc (-1 : ℝ) 1) :
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
  haveI : Infinite (Set.Icc (-1 : ℝ) 1) := Set.Icc.infinite (by norm_num)
  let q : ∀ i : ℕ, C(K, Bool) := fun i => ⟨fun k => k i, continuous_apply i⟩
  have hsep : Function.Injective (fun k : K => fun i => q i k) := by
    intro k l h
    exact funext (fun i => congrFun h i)
  refine ⟨s, hinj, Set.infinite_range_of_injective hinj, hparts, hc, fun ε hε => ?_⟩
  obtain ⟨J, hJ⟩ := exists_uniform_finite_readout_variation q hsep s
    (fun a => (hparts a).1) (fun a => (hparts a).2) hc ε hε
  refine ⟨J, fun a => ?_⟩
  have h := hJ a
  change (s a).totalVariation.real univ - ε <
    (SignedMeasure.totalVariation
      ((s a).map (finiteObservationReadout (fun i (x : K) => x i) J))).real univ ∧
    (SignedMeasure.totalVariation
      ((s a).map (finiteObservationReadout (fun i (x : K) => x i) J))).real univ ≤
        (s a).totalVariation.real univ at h
  constructor <;> linarith [h.1, h.2]

#print axioms review_exact_statement
#print axioms review_cantor_signed_interval
#print axioms D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation
