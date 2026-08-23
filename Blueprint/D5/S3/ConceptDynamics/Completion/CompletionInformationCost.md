# Information Cost of Concept Completion

## Abstract

Completion cost is conditional entropy on supported concept fibers, not a global factorization criterion.

**Theorem 1.1 (Completion cost is conditional entropy).**

$$\begin{gathered}\forall X, C, K\ [\operatorname{Fintype}(X)] [\operatorname{Fintype}(C)] [\operatorname{Fintype}(K)],\\{}mass: X \to \mathbb{R}, concept: X \to C, target: X \to K,\\{}(\forall x, 0 \leq mass(x)) \land \sum_{x}mass(x) = 1 \Rightarrow \\{}\operatorname{shannonEntropy}(\operatorname{completionLaw}\left(mass, concept, target\right)) - \operatorname{shannonEntropy}(\operatorname{pushforward}\left(concept, mass\right)) = \operatorname{conditionalEntropy}(\operatorname{completionLaw}\left(mass, concept, target\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/CompletionInformationCost.completion_information_cost` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a normalized nonnegative mass be given on a finite source, with a concept readout and a target readout. Their completion law is the joint distribution obtained by sending each source point to its pair of readout values.

The first marginal of this joint law is exactly the distribution of the concept readout. The finite entropy chain rule therefore identifies the entropy gained by adjoining the target coordinate with the target's entropy conditional on the current concept.

Only concept fibers carrying positive mass contribute to this cost. No strict positivity assumption is imposed on individual source points or concept fibers.

**Lemma 1.2 (Zero completion cost need not give a global target factor).**

$$\begin{gathered}\exists mass: \operatorname{Fin}\left(3\right) \to \mathbb{R}, concept, target: \operatorname{Fin}\left(3\right) \to Bool,\\{}(\forall x, 0 \leq mass(x)) \land \sum_{x}mass(x) = 1 \land \\{}\operatorname{conditionalEntropy}(\operatorname{completionLaw}\left(mass, concept, target\right)) = 0 \land \\{}(\neg \exists factor: Bool \to Bool, target = factor \circ concept) \land \\{}\exists x, y: \operatorname{Fin}\left(3\right), mass(x) = 0 \land mass(y) = 0 \land \\{}concept(x) = concept(y) \land target(x) \neq target(y).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Completion/CompletionInformationCost.zero_conditional_entropy_not_global_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a three-point source, put all mass on the first point, use the constant false concept readout, and let the target be false on the first two points and true on the third. The only supported conditional slice is a point mass, so its conditional entropy is zero.

The two zero-mass points have the same concept value but different target values. Consequently no Boolean function can recover the target from the concept on the whole source type. Zero completion cost therefore controls supported fibers only, not unsupported points.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Completion/CompletionInformationCost.completion_information_cost`
- Truth anchor: `D5/S3/ConceptDynamics/Completion/CompletionInformationCost.zero_conditional_entropy_not_global_factorization`
- Dependency: [D5/S3/Entropy/ConditionalEntropyEquality](../../Entropy/ConditionalEntropyEquality.md)
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../../Entropy/Forgetting/CapacityMonotone.md)
