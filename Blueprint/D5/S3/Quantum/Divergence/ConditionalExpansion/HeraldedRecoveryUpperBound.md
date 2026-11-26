# Heralded recovery upper bound

## Abstract

The success probability of explicit heralded recovery bounds conditional trace expansion.

**Definition 1.1 (Bell-kernel recovery map).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryUpperBound.bellKernelRecovery`

*Formalization.* `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryUpperBound.bellKernelRecovery` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let P be the normalized Bell projector and let Q project onto the kernel of amp N(I − P). The completely positive map sums congruences by the conjugate reshaping of each column of Q divided by √d.

**Theorem 1.2 (Finite-channel upper bound from heralded recovery).**

Lean statement: `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryUpperBound.heralded_recovery_upper_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryUpperBound.heralded_recovery_upper_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Christoph Hirche; Ian George; Theshani Nuradha; Mark M. Wilde (2026). *Conditional contraction coefficients and their applications to quantum networks*. URL: <https://arxiv.org/abs/2608.27171v1>.

*Commentary.*

For every finite channel N from A to B with d = |A| ≥ 2, let P be the normalized Bell projector, X₀ = amp N(P), and Q the orthogonal projection onto the kernel of amp N(I − P). The columns of Q give a rank-one decomposition because QQᴴ = Q. Conjugate reshaping of those columns gives the Kraus family of a completely positive map from B to A.

The map is trace nonincreasing on every positive semidefinite input. Its composition with N sends every complex matrix X to pX, with p = Re Tr(QX₀)/d² in the interval [0, 1]. Thus on each normalized state the branch succeeds with probability p, independently of the input state.

For every ε > 0 there are orthogonal density states on the reference Option A and the input A, with positive input gap and actual conditional trace-gap ratio strictly below d²p + ε. Taking the infimum yields η ≤ d²p, and p is feasible for the supremal probability of heralded exact recovery. Equation (2.42) of Hirche, George, Nuradha and Wilde defines the coefficient compared here.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryUpperBound.bellKernelRecovery`
- Truth anchor: `D5/S3/Quantum/Divergence/ConditionalExpansion/HeraldedRecoveryUpperBound.heralded_recovery_upper_bound`
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/BellKernelLimit](BellKernelLimit.md)
- Dependency: [D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery](DirectBellKrausRecovery.md)
