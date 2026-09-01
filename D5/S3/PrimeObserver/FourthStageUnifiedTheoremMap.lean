/- GID: D5/S3/PrimeObserver/FourthStageUnifiedTheoremMap
   generality: G
   mirror-B: D5/B/S3/PrimeObserver/FourthStageUnifiedTheoremMap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Observable algebras, finite quotients, coding, class groups, and traces form the fourth-stage theorem map. -/

import D5.S0.Observation.PowerTraceCharacteristicPolynomialSaturation
import D5.S0.Observation.PowerTraceSimilarityCountermodel
import D5.S3.Arith.Coding.ErrorErasureUniqueDecoding
import D5.S3.Arith.Coding.ExactResidueCodeMinimumDistance
import D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraRepresentation
import D5.S3.ConceptDynamics.RefinementAlgebra.PullbackAlgebraRefinementDuality
import D5.S3.Factorization.Galois.ClassFunctionSeparationRate
import D5.S3.Factorization.IdealClassGroups.ClassGroupQuotientUniversality
import D5.S3.Factorization.PrimePowers.FinitePrimePowerQuotientCompleteness

/- Library-search audit trail (2026-09-02):
   * Exact owners for all nine clauses are imported and applied directly; searches by
     name, symbol variants, theorem shape, digestion receipt, digest, generalized owner,
     and in-flight branch found no existing theorem packaging this map.
   * The prime-density arrow is restricted to the proved finite conjugacy-class rate:
     neither D5 nor pinned Mathlib supplies the absent Chebotarev transfer hypotheses.
   * The carrier-free valuation sequence is replaced by the class-group quotient
     universal property under `CommRing` and `IsDedekindDomain` assumptions.
   * Unconditional trace recovery of characteristic polynomials over arbitrary fields
     is not asserted; Cayley-Hamilton saturation and an explicit Jordan countermodel
     record the valid positive and negative spectral conclusions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.PrimeObserver.FourthStageUnifiedTheoremMap

open D5.S0.Observation.PowerTraceCharacteristicPolynomialSaturation
open D5.S0.Observation.PowerTraceSimilarityCountermodel
open D5.S3.Arith.Coding.ErrorErasureUniqueDecoding
open D5.S3.Arith.Coding.ExactResidueCodeMinimumDistance
open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Dialectics.DeterministicInterfaceEquivalence
open D5.S3.ConceptDynamics.RefinementAlgebra.ObservableEventAlgebraRepresentation
open D5.S3.ConceptDynamics.RefinementAlgebra.PullbackAlgebraRefinementDuality
open D5.S3.Factorization.Galois.ClassFunctionSeparationRate
open D5.S3.Factorization.IdealClassGroups.ClassGroupQuotientUniversality
open D5.S3.Factorization.PrimePowers.FinitePrimePowerQuotientCompleteness
open IsLocalization IsFractionRing FractionalIdeal Units
open Polynomial
open scoped nonZeroDivisors

universe u g r h k

/-- A single parameterized package of the fourth-stage observer map. It records the
observable-event representation and refinement duality, the finite-group nilpotence
criterion and exact class-function success rate, exact residue-code distance and
error/erasure uniqueness, class-group quotient universality, and both the positive
Cayley-Hamilton trace saturation law and a concrete non-similarity witness. -/
theorem fourth_stage_unified_theorem_map
    {X O P : Type u} (q : Concept X O) (readout : Concept X P)
    {G : Type g} [Group G] [Fintype G]
    {S : Type*} {first second : G -> S}
    (hinvariant : AreConjugacyInvariantTargets first second)
    (modulus : Nat -> Nat) (n rangeLimit errors erasures : Nat)
    (hmodulus : forall i, i < n -> 2 ≤ modulus i)
    (hstrict : forall i j, i < j -> j < n -> modulus i < modulus j)
    (hcoprime : forall i j, i < n -> j < n -> i ≠ j ->
      Nat.Coprime (modulus i) (modulus j))
    (hRange : 2 ≤ rangeLimit)
    (hRangeUpper : rangeLimit ≤
      D5.S3.Arith.Coding.ResidueCodeDynamicRange.prefixProduct modulus n)
    {Alphabet : Type*} [DecidableEq Alphabet]
    {C : Set (Fin n -> Alphabet)}
    (hC : D5.S3.Arith.Coding.ResidueCodeErrorDetection.MinDistanceAtLeast C
      (n - maximumBlindCoordinateCount modulus n rangeLimit))
    (erased : Finset (Fin n)) (hErased : erased.card ≤ erasures)
    (hBudget : 2 * errors + erasures <
      n - maximumBlindCoordinateCount modulus n rangeLimit)
    (R : Type r) [CommRing R] [IsDedekindDomain R]
    (H : Type h) [Group H]
    (f : (FractionalIdeal R⁰ (FractionRing R))ˣ →* H)
    (principal_eq_one : forall x : (FractionRing R)ˣ,
      f (toPrincipalIdeal R (FractionRing R) x) = 1)
    {KField : Type k} [Field KField] {matrixDim : Nat}
    (M : Matrix (Fin matrixDim) (Fin matrixDim) KField) :
    (∃! representation :
        observableEventBooleanAlgebra q ≃o Set (Set.range q),
      forall event,
        representation event =
          Set.rangeFactorization q '' (event : Set X)) ∧
      (Refines (Set.rangeFactorization q) (Set.rangeFactorization readout) <->
        PullbackAlgebra q ⊆ PullbackAlgebra readout) ∧
      (primePowerResidual G = ⊥ <-> Group.IsNilpotent G) ∧
      (finiteGroupSuccessRate first second =
        (conjugacyClassSeparationCount first second : Rat) / Fintype.card G) ∧
      (residueMinimumDistance modulus n rangeLimit =
        n - maximumBlindCoordinateCount modulus n rangeLimit) ∧
      (forall (trueWord received : Fin n -> Alphabet), trueWord ∈ C ->
        (Finset.univ.filter fun i =>
          i ∉ erased ∧ received i ≠ trueWord i).card ≤ errors ->
        ∃! candidate, candidate ∈ C ∧
          (Finset.univ.filter fun i =>
            i ∉ erased ∧ received i ≠ candidate i).card ≤ errors) ∧
      (∃! descended : ClassGroup R →* H,
        f = descended.comp (ClassGroup.mk (FractionRing R))) ∧
      (M ^ matrixDim =
          -∑ i ∈ Finset.range matrixDim, M.charpoly.coeff i • M ^ i) ∧
      (forall offset : Nat,
        Matrix.trace (M ^ (matrixDim + offset)) =
          -∑ i ∈ Finset.range matrixDim,
            M.charpoly.coeff i * Matrix.trace (M ^ (i + offset))) ∧
      (forall N : Matrix (Fin matrixDim) (Fin matrixDim) KField,
        N.charpoly = M.charpoly ->
        (forall i, i < matrixDim ->
          Matrix.trace (M ^ (i + 1)) = Matrix.trace (N ^ (i + 1))) ->
        forall exponent : Nat,
          Matrix.trace (M ^ (exponent + 1)) =
            Matrix.trace (N ^ (exponent + 1))) ∧
      (∃ A N : Matrix (Fin 2) (Fin 2) KField,
        (forall exponent : Nat, 1 ≤ exponent ->
          Matrix.trace (A ^ exponent) = Matrix.trace (N ^ exponent)) ∧
        A.charpoly = N.charpoly ∧
        A.rank ≠ N.rank ∧
        ¬ ∃ U : (Matrix (Fin 2) (Fin 2) KField)ˣ,
          (U : Matrix (Fin 2) (Fin 2) KField) * A *
            (↑U⁻¹ : Matrix (Fin 2) (Fin 2) KField) = N) := by
  have algebraDuality := pullback_algebra_refinement_duality q readout
  have residualNilpotent :
      primePowerResidual G = ⊥ <-> Group.IsNilpotent G :=
    (finite_prime_power_quotient_completeness_tfae (G := G)).out 1 3
  have countermodel := power_traces_do_not_determine_similarity (K := KField)
  dsimp only at countermodel
  refine ⟨observable_event_algebra_representation q,
    algebraDuality.1.trans algebraDuality.2,
    residualNilpotent,
    finite_group_success_rate_eq_conjugacy_class_count hinvariant,
    exact_residue_code_minimum_distance modulus n rangeLimit hmodulus hstrict
      hcoprime hRange hRangeUpper,
    error_erasure_unique_decoding hC erased hErased hBudget,
    class_group_quotient_universality R H f principal_eq_one,
    (power_trace_characteristic_polynomial_saturation M).1,
    (power_trace_characteristic_polynomial_saturation M).2.1,
    (power_trace_characteristic_polynomial_saturation M).2.2,
    ?_⟩
  refine ⟨0, Matrix.single 0 1 1, ?_, ?_, ?_, ?_⟩
  · intro exponent hExponent
    exact (countermodel.1 exponent hExponent).1.trans
      (countermodel.1 exponent hExponent).2.symm
  · exact countermodel.2.1.trans countermodel.2.2.1.symm
  · rw [countermodel.2.2.2.1, countermodel.2.2.2.2.1]
    exact zero_ne_one
  · exact countermodel.2.2.2.2.2.1

#print axioms fourth_stage_unified_theorem_map

end D5.S3.PrimeObserver.FourthStageUnifiedTheoremMap
