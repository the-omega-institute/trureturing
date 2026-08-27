# Commitment Information Saturation

## Abstract

Complete future recovery saturates the conditional commitment-information bound.

**Theorem 1.1 (Complete recovery saturates commitment information).**

$$\begin{gathered}\forall X: Type, E: Type, C: Type, B: Type,\\{}[\operatorname{Fintype}(X)], [\operatorname{Fintype}(E)], [\operatorname{Fintype}(C)], [\operatorname{Fintype}(B)],\\{}\mu: X \to \mathbb{R}, e: X \to E,\\{}c: X \to C, b: X \to B,\\{}((\forall x\in X, 0 \leq \mu(x)) \land \operatorname{targetResidualEntropy}(\mu, x \mapsto (e(x), b(x)), c) = 0) \Rightarrow\\{}\operatorname{conditionalMutualInformation}(\operatorname{pushforward}(x \mapsto (e(x), (c(x), b(x))), \mu)) = \operatorname{targetResidualEntropy}(\mu, e, c).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/CommitmentInformationSaturation.commitment_information_saturation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonnegative finite sample mass constructs the environment, current commitment, and future behavior records through their joint pushforward law.

When the commitment has zero conditional entropy after observing the paired environment-future record, its conditional mutual information with the future equals its entropy given only the environment.

## References

- Truth anchor: `D5/S3/Entropy/Forgetting/CommitmentInformationSaturation.commitment_information_saturation`
- Dependency: [D5/S3/Entropy/Forgetting/ConditionalInformationForgetting](ConditionalInformationForgetting.md)
