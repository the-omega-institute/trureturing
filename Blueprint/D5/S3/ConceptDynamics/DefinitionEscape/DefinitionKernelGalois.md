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

**Theorem 1.2 (Escaping the semantic closure is exactly having a kernel witness).**

$$\forall X, InputOutput, Output: Type,\ Gamma: \operatorname{Set}\left(\operatorname{Concept}\left(X, InputOutput\right)\right), target: \operatorname{Concept}\left(X, Output\right),\ \neg(target \in \operatorname{SemanticClosure}\left(Gamma\right)) \iff \exists left, right: X, (\forall definition: Gamma, \operatorname{definition}\left(left\right) = \operatorname{definition}\left(right\right)) \land \operatorname{target}\left(left\right) \neq \operatorname{target}\left(right\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois.not_mem_semanticClosure_iff_kernel_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A readout lies outside the semantic closure of a family exactly when some pair of points is identified by every member of the family yet separated by the readout.

Both directions reuse the fiber-constancy characterisation of the closure. No new kernel, separator, or replacement readout is introduced.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois.definition_relation_galois`
- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois.not_mem_semanticClosure_iff_kernel_witness`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction](BlindKernelObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw](ResidualJoinLaw.md)
