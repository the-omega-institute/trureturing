# Finite Fejer Near-Collision Bounds

## Abstract

Finite Fejer kernels give exact Fourier energy identities and explicit collision bounds.

For M at least one, F_M is the Fejer cosine polynomial, S_M(t) is the length-M exponential sum, E_M(gamma) is the ordered pair energy, N_M(gamma) is the filtered ordered near-pair set, and mult_gamma(v) is the cardinality of the fiber gamma^{-1}(v).

**Theorem 1.1 (The Fejer kernel is a normalized square).**

$$\forall M \in \mathbb{N}, t \in \mathbb{R},\; 1 \le M \Rightarrow \operatorname{F}\left(M, t\right) = \frac{1}{M} \cdot \left\lVert \operatorname{S}\left(M, t\right) \right\rVert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_square` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural M and real t, the Fejer kernel equals one over M times the squared norm of the geometric exponential sum.

The proof grows the exponential sum by one endpoint. Expanding the new norm square produces the next triangular autocorrelation row; normalization then gives the stated Fejer polynomial.

**Theorem 1.2 (Pair energy is signed Fourier energy).**

$$\forall n \in \mathbb{N}, M \in \mathbb{N}, g \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; 1 \le M \Rightarrow \operatorname{E}\left(M, g\right) = \sum_{k \in \mathbb{Z} \land \left|k\right| < M} \left(1 - \frac{\left|k\right|}{M}\right) \cdot \left\lVert \sum_{i \in \operatorname{Fin}\left(n\right)} \operatorname{phase}\left(k \cdot g_{i}\right) \right\rVert^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_energy_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a family indexed by Fin n, the total ordered pair energy is the sum over every integer mode with absolute value below M, weighted by 1-|k|/M, of the squared exponential-sum norm.

The proof partitions the signed finite sum into its zero, positive, and negative ranges. Each cosine pair sum becomes a complex norm square, and conjugation identifies the two nonzero signs.

**Theorem 1.3 (The Fejer kernel is large on its central window).**

$$\forall M \in \mathbb{N}, t \in \mathbb{R},\; \left(1 \le M \land \left|t\right| \le \frac{\pi}{M}\right) \Rightarrow \frac{4 \cdot M}{\pi^{2}} \le \operatorname{F}\left(M, t\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_local_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inside |t| <= pi/M, the Fejer kernel is at least 4M/pi^2.

The proof treats t=0 directly and otherwise combines the geometric-sum identity with the lower sine estimate on [-pi/2,pi/2] and the global upper estimate |sin y| <= |y|. Squaring yields the exact constant 4/pi^2.

**Theorem 1.4 (Fejer energy controls ordered near collisions).**

$$\forall n \in \mathbb{N}, M \in \mathbb{N}, g \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; 1 \le M \Rightarrow \operatorname{card}\left(\operatorname{N}\left(M, g\right)\right) \le \frac{\pi^{2}}{4 \cdot M} \cdot \operatorname{E}\left(M, g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.near_pair_count_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of ordered pairs separated by at most pi/M is bounded by pi^2/(4M) times the total Fejer energy.

The proof sums the local lower bound over the filtered near-pair set, then uses the global square representation to add the nonnegative contribution of every remaining ordered pair.

**Theorem 1.5 (Fejer energy dominates squared multiplicities).**

$$\forall n \in \mathbb{N}, M \in \mathbb{N}, g \in \operatorname{Fin}\left(n\right) \to \mathbb{R},\; 1 \le M \Rightarrow M \cdot \sum_{v \in \operatorname{image}\left(g\right)} \operatorname{mult}\left(g, v\right)^{2} \le \operatorname{E}\left(M, g\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.distinct_multiplicity_energy_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The total energy is at least M times the sum of squared fiber multiplicities over the distinct values attained by gamma.

Equal-value ordered pairs form disjoint fiber blocks. On every such block the argument is zero and F_M(0)=M; fiberwise reindexing turns the resulting index sum into the displayed distinct-value sum.

This finite deterministic inequality supplies no zeta-zero asymptotic and no positive proportion of simple zeros without a separate upper bound for the Fejer energy.

## References

- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.distinct_multiplicity_energy_lower_bound`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_energy_identity`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_local_lower_bound`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.fejer_square`
- Truth anchor: `D5/S3/Zeros/Repulsion/FejerNearCollisionBound.near_pair_count_bound`
