# Affine-budget causal witnesses and robust query decisions

## Abstract

The checked affine presentation preserves the original causal constraint system and target with a smaller support budget. Separate residual certificates control decisions for queries outside the retained family.

**Theorem 1.1 (Original-carrier witness with reduced support budget).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.checked_affine_causal_witness`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.checked_affine_causal_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Acceptance reconstructs all original rows and the target, packages the computed result as FiniteResponseLaw and bounds its support by the selected coordinate count plus one.

**Theorem 1.2 (Preserve the exact lower endpoint and its dual).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.checked_affine_lower_endpoint`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.checked_affine_lower_endpoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The existing lower dual certificate is reused with the smaller checked primal witness. No inequality or objective coefficient is altered.

**Theorem 1.3 (Transfer a strict decision with a certified margin).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.checked_compressed_query_decision`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.checked_compressed_query_decision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the compressed query exceeds the threshold by more than the checked residual width, the original query also exceeds it. The bound concerns finite model approximation, not sampling uncertainty.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.checked_affine_causal_witness`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.checked_affine_lower_endpoint`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/RankAdaptiveSparseCausalWitness.checked_compressed_query_decision`
- Dependency: [D5/S0/Certificates/RationalMomentQueryEnvelope](../../../S0/Certificates/RationalMomentQueryEnvelope.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness](CertifiedSparseCausalWitness.md)
