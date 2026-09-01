# Epsilon Self-Dimension

## Abstract

For a decreasing singular-value profile, epsilon self-dimension is the number of singular values strictly above epsilon.

**Theorem 1.1 (The first acceptable rank equals the strict threshold count).**

$$\forall sigma, e: N \to R, epsilon \in R,\\{}Antitone(sigma) \land {\forall i \in N, 0 \leq sigma(i)} \land\\{}{\exists k \in N, e(k) \leq epsilon} \land\\{}{\forall k \in N, e(k) = sigma(k)} \Rightarrow\\{}min(\{k \in N \mid e(k) \leq epsilon\}) = ncard(\{i \in N \mid epsilon < sigma(i)\}).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/LinearMemory/EpsilonSelfDimension.epsilon_self_dimension_eq_threshold_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Eckart-Young approximation identity is an explicit premise. The proof uses only the antitone order of the zero-indexed singular values: the values strictly above epsilon form the initial interval before the first acceptable rank.

Nonemptiness of the acceptable-rank set is explicit, so the minimum has no empty-set convention. Zero-based sigma(k) corresponds to the source's one-based sigma_(k+1), and strict greater-than complements less-than-or-equal at equality thresholds.

## References

- Truth anchor: `D5/S3/Observer/LinearMemory/EpsilonSelfDimension.epsilon_self_dimension_eq_threshold_count`
