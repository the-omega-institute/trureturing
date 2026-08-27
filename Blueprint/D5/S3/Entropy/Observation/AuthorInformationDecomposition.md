# Author Information Decomposition

## Abstract

Conditional action entropy splits into internal-state information and residual entropy.

**Theorem 1.1 (Internal-state information decomposes conditional action entropy).**

$$\begin{aligned}\forall Public, Action, Memory: \operatorname{Type},\\(\operatorname{Fintype}\left(Public\right) \land \operatorname{Fintype}\left(Action\right) \land \operatorname{Fintype}\left(Memory\right)),\\jointLaw: \operatorname{Prod}\left(Public, \operatorname{Prod}\left(Action, Memory\right)\right) \to \mathbb{R}, \forall z: \operatorname{Prod}\left(Public, \operatorname{Prod}\left(Action, Memory\right)\right), 0 \leq \operatorname{jointLaw}\left(z\right) \Rightarrow\\\operatorname{let} actionGivenPublicLaw := \operatorname{xyProjection}\left(jointLaw\right),\\\operatorname{let} actionGivenPublicMemoryLaw: \operatorname{Prod}\left(\operatorname{Prod}\left(Public, Memory\right), Action\right) \to \mathbb{R} := z \mapsto \operatorname{jointLaw}\left(\operatorname{pair}\left(\operatorname{fst}\left(\operatorname{fst}\left(z\right)\right), \operatorname{pair}\left(\operatorname{snd}\left(z\right), \operatorname{snd}\left(\operatorname{fst}\left(z\right)\right)\right)\right)\right),\\\operatorname{conditionalEntropy}\left(actionGivenPublicLaw\right) = \operatorname{conditionalMutualInformation}\left(jointLaw\right) + \operatorname{conditionalEntropy}\left(actionGivenPublicMemoryLaw\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/AuthorInformationDecomposition.author_information_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Public, Action, and Memory be arbitrary finite carriers. The nonnegative joint mass is ordered as Public times (Action times Memory), matching the conditioning coordinate used by the canonical finite entropy interface.

The public-action law is the canonical projection that sums out Memory. The action-given-public-and-memory law is constructed by reindexing the same joint mass onto (Public times Memory) times Action; it is not defined from the target equality.

Applying the entropy chain rule before and after that reindexing shows that action entropy given Public equals conditional mutual information between Action and Memory given Public, plus the action entropy remaining after Memory is also known.

The two explanatory bullets following the source's boxed identity are interpretive labels for its summands, not additional mathematical clauses.

## References

- Truth anchor: `D5/S3/Entropy/Observation/AuthorInformationDecomposition.author_information_decomposition`
- Dependency: [D5/S3/Entropy/Submodularity/ConditionalMutualInformation](../Submodularity/ConditionalMutualInformation.md)
