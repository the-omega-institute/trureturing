# Deterministic Output Entropy Rate

## Abstract

A finite deterministic output process has no conditional entropy injection and zero normalized output-entropy rate.

**Theorem 1.1 (Deterministic output blocks have a fixed entropy budget and zero rate).**

$$\begin{gathered}\forall Y: \operatorname{Type}, O: \operatorname{Type}, Theta: \operatorname{Type},\\{}[\operatorname{Fintype}\left(Y\right)], [\operatorname{Fintype}\left(O\right)], [\operatorname{Fintype}\left(Theta\right)],\\{}F: Y \to Y, q: Y \to O, p: Y \to \mathbb{R},\\{}G: Theta \to \left(Y \to Y\right), r: Theta \to \left(Y \to O\right),\\{}w: Theta\times Y \to \mathbb{R},\\{}((\forall y, 0 \leq p(y)) \land \sum_{y}p(y) = 1) \land ((\forall z, 0 \leq w(z)) \land \sum_{z}w(z) = 1) \Rightarrow\\{}(\forall T\in \mathbb{N}, \operatorname{conditionalEntropy}\left(\operatorname{pushforward}\left(y\mapsto (y, \operatorname{outputBlock}\left(F, q, T, y\right)), p\right)\right) = 0) \land\\{}(\forall T\in \mathbb{N}, \operatorname{shannonEntropy}\left(\operatorname{pushforward}\left(y\mapsto \operatorname{outputBlock}\left(F, q, T, y\right), p\right)\right) \leq \operatorname{shannonEntropy}\left(p\right) \leq \log(\lvert Y \rvert)) \land\\{}\lim_{T \to \infty} \frac{\operatorname{shannonEntropy}\left(\operatorname{pushforward}\left(y\mapsto \operatorname{outputBlock}\left(F, q, T, y\right), p\right)\right)}{T+1} = 0 \land\\{}(\forall T\in \mathbb{N}, \operatorname{conditionalEntropy}\left(\operatorname{pushforward}\left(z\mapsto (z, \operatorname{configuredOutputBlock}\left(G, r, T, z\right)), w\right)\right) = 0) \land\\{}(\forall T\in \mathbb{N}, \operatorname{shannonEntropy}\left(\operatorname{pushforward}\left(z\mapsto \operatorname{configuredOutputBlock}\left(G, r, T, z\right), w\right)\right) \leq \operatorname{shannonEntropy}\left(w\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/DeterministicOutputEntropyRate.deterministic_output_entropy_budget_and_rate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a normalized nonnegative mass on a finite state carrier choose the initial state of a deterministic update and readout. The block outputBlock contains the readouts at every time from zero through the chosen horizon and is constructed directly by function iteration.

For every horizon, the graph law of the initial state and its output block has zero conditional entropy. Deterministic pushforward cannot increase Shannon entropy, and the initial entropy is bounded by the logarithm of the state-cardinality. The bounded numerator divided by the growing block length therefore tends to zero.

A second normalized law may jointly sample a finite configuration and initial state. The configured block keeps that sampled configuration fixed at every time. Its graph conditional entropy is zero and its output entropy is bounded by the joint configuration-state entropy. All entropy values and logarithms use the repository's canonical natural-logarithm convention.

## References

- Truth anchor: `D5/S3/Entropy/Forgetting/DeterministicOutputEntropyRate.deterministic_output_entropy_budget_and_rate`
- Dependency: [D5/S3/Entropy/Forgetting/DeterministicEntropyEquality](DeterministicEntropyEquality.md)
