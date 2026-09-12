# Partial Function Domain Observation

## Abstract

Two states agree in every jointly successful context, but a partial operation succeeds at only one of them.

There are two states, a and b. The readout q takes values in the two-element type Fin 2 and is constantly zero. The single unary operation fixes a and is undefined at b. A context is any finite iteration of that operation, including the identity at depth zero. Failure propagates through every further operation.

An observation has type Option (Fin 2). A successful zero is some zero, representing the tagged pair (1,0); failure is the distinct none tag. The success tag records definedness, not a numerical encoding of the resulting state.

**Theorem 1.1 (Exact observations at every finite depth).**

Lean statement: `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.context_observation_profile`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.context_observation_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a, every context succeeds and reads zero. At b, only the depth-zero identity succeeds; every positive depth fails. Induction on the context length proves this for all natural depths.

**Theorem 1.2 (The partial domain is not a union of readout fibers).**

Lean statement: `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.partial_domain_not_q_saturated`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.partial_domain_not_q_saturated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The domain is the singleton containing a. The two states have equal q readings but different domain membership, so that singleton is not saturated under q.

**Theorem 1.3 (Common-success agreement fails to preserve definedness).**

Lean statement: `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.common_success_domain_refutation`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.common_success_domain_refutation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CommonSuccessPreservesDomains asserts that states agreeing in every jointly successful context have equal membership in the operation domain. The pair a,b refutes that assertion: every shared successful reading is zero, but the operation is defined only at a.

**Theorem 1.4 (The complete two-state counterexample).**

Lean statement: `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.partial_function_domain_counterexample`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.partial_function_domain_counterexample` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem combines the constant readout, its failure to reach one in Fin 2, the two operation values, the singleton domain, agreement in all jointly successful contexts, and both failures of domain preservation. At depth one the full observations are some zero and none, and these are unequal.

Replacing none by the ordinary readout zero makes the observations of a and b equal again at every finite depth. Thus recording a failed observation and recording a successful zero are different requirements.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.common_success_domain_refutation`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.context_observation_profile`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.partial_domain_not_q_saturated`
- Truth anchor: `D5/S3/ConceptDynamics/Observation/PartialFunctionDomainObservation.partial_function_domain_counterexample`
