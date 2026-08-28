# Commitment Information Upper Bound

## Abstract

Conditional commitment information is bounded by commitment entropy given environment.

**Theorem 1.1 (The commitment channel is bounded by conditional commitment entropy).**

$$\begin{gathered}\forall X: Type, E: Type, C: Type, B: Type,\\{}[\operatorname{Fintype}(X)], [\operatorname{Fintype}(E)], [\operatorname{Fintype}(C)], [\operatorname{Fintype}(B)],\\{}\mu: X \to \mathbb{R}, e: X \to E,\\{}c: X \to C, b: X \to B,\\{}((\forall x\in X, 0 \leq \mu(x)) \land \sum_{x \in X} \mu(x) = 1) \Rightarrow\\{}\operatorname{conditionalMutualInformation}(\operatorname{pushforward}(x \mapsto (e(x), (c(x), b(x))), \mu)) \leq \operatorname{targetResidualEntropy}(\mu, e, c).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/CommitmentInformationUpperBound.commitment_information_le_residual_entropy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A normalized nonnegative mass on a finite sample carrier constructs the environment, current commitment, and future behavior through their canonical joint pushforward law.

Enriching the future record with the commitment makes recovery exact, so the frozen saturation theorem identifies its information with the commitment entropy remaining after the environment readout.

Forgetting the added commitment coordinate recovers the actual future record. The frozen deterministic-forgetting theorem then gives the displayed upper bound.

## References

- Truth anchor: `D5/S3/Entropy/Forgetting/CommitmentInformationUpperBound.commitment_information_le_residual_entropy`
- Dependency: [D5/S3/Entropy/ConditionalEntropyEquality](../ConditionalEntropyEquality.md)
- Dependency: [D5/S3/Entropy/Forgetting/CommitmentInformationSaturation](CommitmentInformationSaturation.md)
