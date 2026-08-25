# Definition Kernel Galois

## Abstract

Family kernels form a Galois connection detecting primitive and productive escape.

**Theorem 1.1 (Definition families and relations form a Galois connection).**

$$\operatorname{Subset}\left(Gamma, \operatorname{RelationInvariantReadouts}\left(relation\right)\right) \iff \operatorname{Subset}\left(relation, \operatorname{jointKernel}\left(\operatorname{definitionReadout}\left(Gamma\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois.definition_relation_galois` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem reuses the canonical RelationInvariantReadouts and jointKernel carriers. A family is invariant on a relation exactly when the relation is contained in the common kernel of every family member.

The two implications unpack the same pairwise equality in opposite directions. No auxiliary kernel or replacement readout is introduced.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois.definition_relation_galois`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction](BlindKernelObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw](ResidualJoinLaw.md)
