# Complete checked sparse causal witnesses

## Abstract

Restricting the existing rational moment construction to the initial support yields a sparse witness with no new atoms. Such a witness has a checked zero-or-one-step representation, while accepted traces preserve the original causal LP semantics.

**Theorem 1.1 (Select only initially supported causal atoms).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.exists_supported_moment_replacement`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.exists_supported_moment_replacement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the existing rational Caratheodory construction to the support subtype, then push the small latent law back to the original carrier. All nominated moments and hard support exclusions are preserved.

**Theorem 1.2 (Completeness of the finite certificate language).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.exists_accepted_moment_certificate`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.exists_accepted_moment_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Already sparse inputs use an empty trace. Otherwise the difference from a supported sparse replacement is a valid null direction with pivot ratio one. This existence proof does not supply an executable discovery algorithm.

**Definition 1.3 (Finite array adapter for original rows and query).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.rowQueryArray`

*Formalization.* `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.rowQueryArray` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Coordinate zero holds the original objective; successor coordinates hold the original LP rows. This adapter changes no coefficient or feasibility semantics.

**Theorem 1.4 (Return a sparse law for the unchanged causal problem).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.checked_causal_problem_witness`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.checked_causal_problem_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An accepted trace packages its actual output as FiniteResponseLaw on the original carrier, retains all LinearFeasible constraints and the exact objective, and bounds support by the row count plus two.

**Theorem 1.5 (Reuse the original lower dual certificate).**

Lean statement: `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.checked_lower_endpoint_witness`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.checked_lower_endpoint_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The checked sparse output remains an attaining primal witness. The existing lower-bound certificate theorem certifies the same exact endpoint without altering its constraint system.

## References

- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.checked_causal_problem_witness`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.checked_lower_endpoint_witness`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.exists_accepted_moment_certificate`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.exists_supported_moment_replacement`
- Truth anchor: `D5/S3/ConceptDynamics/CausalMoments/CertifiedSparseCausalWitness.rowQueryArray`
- Dependency: [D5/S0/Certificates/RationalMomentReplay](../../../S0/Certificates/RationalMomentReplay.md)
- Dependency: [D5/S3/ConceptDynamics/CausalMoments/FiniteMomentSparseLaw](FiniteMomentSparseLaw.md)
