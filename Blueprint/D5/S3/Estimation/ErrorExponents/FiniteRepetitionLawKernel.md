# Finite Repetition Preserves the Law Kernel

## Abstract

Finite independent repetition amplifies genuine differences without separating equal one-shot laws.

**Theorem 1.1 (Finite repetition amplifies without crossing the law kernel).**

$$\begin{gathered}\forall S, O: \operatorname{Type}(), [\operatorname{Fintype}(O)],\\{}\forall K: S \to O \to \mathbb{R},\\{}\forall x, y: S, n: \mathbb{N},\\{}((\forall i, 0 \le \operatorname{K}(x, i)) \land \sum_{i} \operatorname{K}(x, i) = 1) \land\\{}((\forall i, 0 \le \operatorname{K}(y, i)) \land \sum_{i} \operatorname{K}(y, i) = 1) \land 0 < n \Rightarrow\\{}[((1 < n \land 0 < \operatorname{Bhattacharyya}(K_{x}, K_{y}) \land \operatorname{Bhattacharyya}(K_{x}, K_{y}) < 1) \Rightarrow \operatorname{Bhattacharyya}(\operatorname{IidPower}(K_{x}, n), \operatorname{IidPower}(K_{y}, n)) < \operatorname{Bhattacharyya}(K_{x}, K_{y})) \land\\{}(\operatorname{IidPower}(K_{x}, n) = \operatorname{IidPower}(K_{y}, n) \iff K_{x} = K_{y})].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/ErrorExponents/FiniteRepetitionLawKernel.finite_repetition_amplifies_without_crossing_law_kernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The repeated experiment is the repository's canonical independent product law. Exact multiplicativity turns its Bhattacharyya affinity into the n-th power of the one-copy affinity, which is strictly smaller when at least two copies are taken and the one-copy affinity lies strictly between zero and one.

For the equality clause, summing a positive-copy product law over all tail coordinates recovers its first marginal because each tail law has total mass one. Equality of repeated laws therefore forces equality of the one-shot laws; the reverse direction is preserved by the same canonical product construction.

## References

- Truth anchor: `D5/S3/Estimation/ErrorExponents/FiniteRepetitionLawKernel.finite_repetition_amplifies_without_crossing_law_kernel`
- Dependency: [D5/S3/Estimation/BhattacharyyaExponent](../BhattacharyyaExponent.md)
