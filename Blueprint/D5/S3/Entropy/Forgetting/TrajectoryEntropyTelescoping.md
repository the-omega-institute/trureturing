# Entropy Telescoping along Deterministic Trajectories

## Abstract

Stepwise reverse conditional entropy exactly accounts for entropy lost along a deterministic finite trajectory.

**Theorem 1.1 (Deterministic trajectory entropy telescopes).**

$$\begin{gathered}\forall k \geq 1, H(p_{k-1}) - H(p_{k}) = H(p_{k-1} \mid p_{k}),\\\forall N, H(p_{0}) - H(p_{N}) = \sum_{k=1}^{N} H(p_{k-1} \mid p_{k}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Forgetting/TrajectoryEntropyTelescoping.deterministic_trajectory_entropy_telescoping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Y be finite, let update : Y -> Y be deterministic, and let the initial mass function be nonnegative and normalized. Define p_k by repeatedly pushing p_0 forward through update. For every positive k, the entropy lost from p_(k-1) to p_k is the conditional entropy of the previous state given the current state.

The transition joint law is constructed on the graph of update, with the current state first and the previous state second. Its first marginal is p_k and its joint entropy is H(p_(k-1)). Applying the repository's finite entropy chain rule directly gives the one-step equality.

Summing the one-step equality over k = 1 through N cancels all intermediate entropies and proves the finite telescoping identity, including N = 0. The construction encodes the source's deterministic trajectory rather than assuming the entropy identity or defining a loss from its target.

Pinned-library searches for finite Shannon conditional entropy, finite entropy chain rules, and deterministic pushforwards found no matching theorem. The repository search found the exact entropy_chain_rule dependency and the pushforward construction, which are imported and applied.

## References

- Truth anchor: `D5/S3/Entropy/Forgetting/TrajectoryEntropyTelescoping.deterministic_trajectory_entropy_telescoping`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](CapacityMonotone.md)
