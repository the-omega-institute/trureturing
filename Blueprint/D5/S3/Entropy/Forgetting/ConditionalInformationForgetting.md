# Conditional Information under Forgetting

## Abstract

Deterministic forgetting of future behavior cannot increase its conditional information about the current commitment.

**Theorem 1.1 (Forgetting future records cannot increase conditional information).**

$$\begin{gathered}\forall X, E, C, B, B': \operatorname{Type},\\{}[\operatorname{Fintype}(X)], [\operatorname{Fintype}(E)], [\operatorname{Fintype}(C)], [\operatorname{Fintype}(B)], [\operatorname{Fintype}(B')],\\{}\mu: X \to \mathbb{R}, (\forall x\in X, 0 \leq \mu(x)) \land \sum_{x} \mu(x) = 1,\\{}e: X \to E, c: X \to C,\\{}b: X \to B, g: B \to B',\\{}\operatorname{conditionalMutualInformation}(\operatorname{pushforward}(x \mapsto (e(x), (c(x), g(b(x)))), \mu)) \leq \operatorname{conditionalMutualInformation}(\operatorname{pushforward}(x \mapsto (e(x), (c(x), b(x))), \mu)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/ConditionalInformationForgetting.conditional_information_forgetting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sample law constructs the joint environment, commitment, and future behavior records. A deterministic map coarsens only the future coordinate while leaving the environment and commitment unchanged.

Conditional mutual information is rewritten as the commitment entropy remaining after the environment minus that remaining after the paired environment-future readout. The frozen deterministic postprocessing theorem makes the latter residual entropy increase, which proves the displayed inequality.

## References

- Truth anchor: `D5/S3/Entropy/Forgetting/ConditionalInformationForgetting.conditional_information_forgetting`
- Dependency: [D5/S3/ConceptDynamics/Communication/TranslationLossMonotonicity](../../ConceptDynamics/Communication/TranslationLossMonotonicity.md)
- Dependency: [D5/S3/Entropy/Submodularity/ConditionalMutualInformation](../Submodularity/ConditionalMutualInformation.md)
