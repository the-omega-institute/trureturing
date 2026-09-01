/- GID: D5/S3/PrimeObserver/LocalReadoutCoreTheoremChain
   generality: G
   mirror-B: D5/B/S3/PrimeObserver/LocalReadoutCoreTheoremChain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Joint kernels, finite certificates, and CRT phase periods form the local-readout theorem chain. -/

import D5.S3.ConceptDynamics.Faithfulness.LocalGlobalResidualCriterion
import D5.S3.Factorization.Periods.CrtPeriodComposition
import D5.S3.ObserverMemory.PredictionCertificates.FiniteDistinguishingCertificate
import D5.S3.PrimeForms.CrossingPeriodicity.SandwichPhasePeriod

/- Library-search audit trail (2026-09-02):
   * Exact D5 owners are `joint_faithfulness_tfae`,
     `local_global_residual_empty_iff_joint_injective`,
     `finite_distinguishing_certificate`, `phase_period_crt_composition`,
     `nonzero_modulus_is_necessary`, and `sandwich_phase_period_package`.
   * Name, symbol-variant, theorem-body, digestion-receipt, digest, generalized-owner,
     and in-flight-branch searches found components but no theorem packaging the chain.
   * The CRT clause requires `m != 0`; its failure at zero is retained as an explicit
     counterexample rather than hidden by Lean's total natural-number division. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeObserver.LocalReadoutCoreTheoremChain

open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion
open D5.S3.ConceptDynamics.Faithfulness.LocalGlobalResidualCriterion
open D5.S3.Factorization.Periods.CrtPeriodComposition
open D5.S3.ObserverMemory.PredictionCertificates.FiniteDistinguishingCertificate
open D5.S3.PrimeForms.Crossing.ExactPropagation
open D5.S3.PrimeForms.Crossing.WindingOrbitZero
open D5.S3.PrimeForms.CrossingPeriodicity.PhaseObserverMinimalPeriod
open D5.S3.PrimeForms.CrossingPeriodicity.SandwichPhasePeriod

universe u v w

/-- The local-readout chain packages kernel separation, residual emptiness, finite
certificates, and crossing-period composition. The nonzero modulus assumption is
necessary, as witnessed by the included zero-modulus counterexample. -/
theorem local_readout_core_theorem_chain
    {I : Type u} {X : Type v} {V : I -> Type w}
    (q : forall i, X -> V i)
    {Protocol Observation Class : Type*} [Finite Class]
    (evaluate : Protocol -> X -> Observation) (available : Set Protocol)
    (classify : X -> Class) (classify_surjective : Function.Surjective classify)
    (class_exact : forall x y,
      classify x = classify y <->
        forall protocol, protocol ∈ available ->
          evaluate protocol x = evaluate protocol y)
    (m : Nat) (hm : m ≠ 0)
    {A : PositiveMatrix} (hA : Admissible A) :
    List.TFAE
        [Function.Injective (jointReadout q),
          forall x y, (forall i, q i x = q i y) -> x = y,
          jointKernel q = diagonal X] ∧
      (IsEmpty {pair : X × X //
          pair.1 ≠ pair.2 ∧
            forall i, q i pair.1 = q i pair.2} <->
        Function.Injective (jointReadout q)) ∧
      (∃ selected : Finset Protocol,
        (selected : Set Protocol) ⊆ available ∧
          forall x y, classify x = classify y <->
            forall protocol, protocol ∈ selected ->
              evaluate protocol x = evaluate protocol y) ∧
      (phasePeriod m =
        m.primeFactors.lcm
          (fun p => phasePeriod (p ^ m.factorization p))) ∧
      ¬(phasePeriod 0 =
        (Nat.primeFactors 0).lcm
          (fun p => phasePeriod (p ^ Nat.factorization 0 p))) ∧
      (windingPhase (crossingSandwich A) = windingPhase A - 2 ∧
        (∀ n : Nat, windingPhase ((crossingSandwich^[n + 6]) A) =
          windingPhase ((crossingSandwich^[n]) A) - 12) ∧
        ∀ p : Nat, 0 < p -> p < 6 ->
          ¬ ∃ j : Int,
            windingPhase ((crossingSandwich^[p]) A) - windingPhase A = 12 * j) := by
  exact ⟨joint_faithfulness_tfae q,
    local_global_residual_empty_iff_joint_injective q,
    finite_distinguishing_certificate evaluate available classify
      classify_surjective class_exact,
    phase_period_crt_composition m hm,
    nonzero_modulus_is_necessary,
    sandwich_phase_period_package hA⟩

#print axioms local_readout_core_theorem_chain

end D5.S3.PrimeObserver.LocalReadoutCoreTheoremChain
