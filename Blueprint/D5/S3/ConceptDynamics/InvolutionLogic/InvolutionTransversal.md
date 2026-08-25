# Involution Transversal

## Abstract

A Boolean orientation of a fixed-point-free involution is an orbit transversal.

**Theorem 1.1 (The transversal law is a preimage-complement equation).**

$$\forall iota: X \to X, S: \operatorname{Set}\left(X\right), \operatorname{OrbitTransversal}\left(iota, S\right) \iff \operatorname{preimage}\left(iota, S\right) = \operatorname{complement}\left(S\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InvolutionLogic/InvolutionTransversal.orbitTransversal_iff_preimage_eq_compl` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OrbitTransversal requires the image of each point to lie in the set exactly when the point itself lies outside it.

Extensionality turns this pointwise biconditional into equality of the set's preimage with its complement.

This equivalence does not assume involutivity; it unfolds the named transversal predicate for the displayed transformation.

**Theorem 1.2 (An involution sends its transversal to the complement).**

$$\forall iota: X \to X, S: \operatorname{Set}\left(X\right), (\operatorname{Involutive}\left(iota\right) \land \operatorname{OrbitTransversal}\left(iota, S\right)) \Rightarrow \operatorname{image}\left(iota, S\right) = \operatorname{complement}\left(S\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InvolutionLogic/InvolutionTransversal.image_eq_compl_of_orbitTransversal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the transformation is involutive and the set is an orbit transversal. A point selected by the set maps outside it.

Conversely, every point outside the set is the image of its own transformed partner, which the transversal law places inside.

Both hypotheses are retained in the antecedent; the image equality is not asserted for an arbitrary transformation or set.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InvolutionLogic/InvolutionTransversal.image_eq_compl_of_orbitTransversal`
- Truth anchor: `D5/S3/ConceptDynamics/InvolutionLogic/InvolutionTransversal.orbitTransversal_iff_preimage_eq_compl`
- Dependency: [D5/S3/ConceptDynamics/InvolutionLogic/AtomicNegationRigidity](AtomicNegationRigidity.md)
