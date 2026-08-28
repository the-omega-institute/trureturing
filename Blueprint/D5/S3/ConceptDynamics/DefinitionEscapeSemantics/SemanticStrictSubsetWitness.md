# Semantic Strict-Expansion Witness

## Abstract

Semantic strict expansion contains a witness in the directed new-domain difference.

**Theorem 1.1 (Strict expansion supplies a new-domain-difference witness).**

$$\operatorname{SemanticStrictSubset}\left(S, J, J'\right) \Rightarrow \exists z, \operatorname{SemanticNewOnly}\left(S, z, J, J'\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticStrictSubsetWitness.semantic_strict_subset_has_new_only_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transport frame interprets domain membership directly. SemanticNewOnly(S,z,J,J') means that z belongs to J' and does not belong to J; it is not an independent black-box predicate.

SemanticStrictSubset(S,J,J') is exactly preservation of membership from J to J' together with existence of a SemanticNewOnly point. The theorem projects that second conjunct without finiteness, inhabitance, decidable equality, or result-uniqueness assumptions.

This discharges obligation 57.3-A from definition-escape-completion-theory atom generic-residual-e8b7049497c6cf0d8b563c5d37805dc2ba0370dd790914983f40359f8fe2d05e. The later certificate and overreach obligations remain separate claims.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeSemantics/SemanticStrictSubsetWitness.semantic_strict_subset_has_new_only_witness`
