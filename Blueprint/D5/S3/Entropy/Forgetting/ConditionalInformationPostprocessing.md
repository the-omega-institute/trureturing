# Conditional Information Postprocessing

## Abstract

Deterministic postprocessing cannot increase finite conditional mutual information.

**Theorem 1.1 (Postprocessing lowers conditional mutual information).**

$$\begin{gathered}\forall C: Type, B: Type, B': Type, E: Type,\\{}\operatorname{Fintype}(C) \land \operatorname{Fintype}(B) \land \operatorname{Fintype}(B') \land \operatorname{Fintype}(E),\\{}p: E \times (C \times B) \to \mathbb{R}, f: B \to B',\\{}(\forall x: E \times (C \times B), 0 \leq p(x)) \land \sum_{x \in E \times (C \times B)} p(x) = 1 \Rightarrow\\{}\operatorname{conditionalMutualInformation}(\operatorname{pushforward}(((e, (c, b)) \mapsto (e, (c, f(b)))), p)) \leq \operatorname{conditionalMutualInformation}(p).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/ConditionalInformationPostprocessing.conditional_mutual_information_postprocessing_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be a finite joint probability law of an environment E, a commitment C, and a future record B.

A deterministic map f from B to B prime constructs the coarse law by pushing p forward along the map that preserves E and C and applies f only to B.

The mutual-information chain rule and finite Markov data processing show that the conditional information between C and the coarse record given E cannot exceed that of the original record.

## References

- Truth anchor: `D5/S3/Entropy/Forgetting/ConditionalInformationPostprocessing.conditional_mutual_information_postprocessing_le`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](CapacityMonotone.md)
- Dependency: [D5/S3/Entropy/Submodularity/MutualInformationChainRule](../Submodularity/MutualInformationChainRule.md)
