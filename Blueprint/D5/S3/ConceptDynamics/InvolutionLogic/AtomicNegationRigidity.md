# Atomic Negation Rigidity

## Abstract

A finite nonempty atomic-negation universe has exactly two elements.

**Theorem 1.1 (Atomic negation exists exactly on a Boolean carrier).**

$$\operatorname{Nonempty}\left(X\right) \Rightarrow (\operatorname{Nonempty}\left(\operatorname{AtomicNegation}\left(X\right)\right) \iff \operatorname{Nonempty}\left(\operatorname{Equiv}\left(X, Bool\right)\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InvolutionLogic/AtomicNegationRigidity.nonempty_iff_equiv_bool` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the carrier is nonempty. An atomic negation assigns each point the unique point different from it.

Choosing one anchor transports such a negation to Boolean negation and yields an equivalence with Bool. Conversely, any Boolean equivalence transports the canonical atomic negation back.

The equivalence is conditional on the displayed Nonempty instance; the statement makes no assertion for an empty carrier.

**Theorem 1.2 (A finite inhabited atomic-negation carrier has two points).**

$$\forall negation: \operatorname{AtomicNegation}\left(X\right), ([\operatorname{Fintype}\left(X\right)] [\operatorname{Nonempty}\left(X\right)]) \Rightarrow \operatorname{card}\left(X\right) = 2.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InvolutionLogic/AtomicNegationRigidity.card_eq_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let negation be an AtomicNegation structure on a finite, inhabited carrier. Its fields force every point other than an anchor to be the anchor's negation.

The induced equivalence with Bool transports finite cardinality, so the carrier has exactly two elements.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InvolutionLogic/AtomicNegationRigidity.card_eq_two`
- Truth anchor: `D5/S3/ConceptDynamics/InvolutionLogic/AtomicNegationRigidity.nonempty_iff_equiv_bool`
