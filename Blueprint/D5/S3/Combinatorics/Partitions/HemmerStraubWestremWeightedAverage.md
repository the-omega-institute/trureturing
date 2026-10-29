# The weighted Hemmer–Straub–Westrem character average

## Abstract

The weighted Ev character averages equal the even binomial value and vanish in odd degrees.

**Definition 1.1 (The reciprocal centralizer weight).**

$$\forall n \in \operatorname{Nat},\; \forall lam \in \operatorname{Nat}.\operatorname{Partition}\left(n\right),\; \operatorname{weight}\left(lam\right) = ((\operatorname{DeformedJucysMurphyC2}.\operatorname{zPartition}\left(lam\right): \operatorname{Rat}))^{-1}$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.weight` (`✓ std3`).

*Citation.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

Section 2, page 4, states: “For a partition λ with part frequencies (1^{m₁}, 2^{m₂}, …, n^{mₙ}), we denote with z_λ = ∏_{j=1}^n j^{mⱼ} mⱼ! the size of the centralizer of a permutation with cycle type λ.” The existing zPartition is this multiplicity product; weight is its reciprocal in Rat.

**Definition 1.2 (The signed even-row average).**

$$\forall n \in \operatorname{Nat},\; \operatorname{leftAverage}\left(n\right) = \sum_{lam: \operatorname{Nat}.\operatorname{Partition}\left(n\right)} (\operatorname{weight}\left(lam\right) \cdot ((\operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((\operatorname{fun}(tau: \operatorname{List}\left(\operatorname{Nat}\right)) \mapsto \sum_{mu \in \operatorname{R3}\left(2 \cdot n\right)} (((-1: \operatorname{Int}))^{\operatorname{List}.\operatorname{length}\left(tau\right)} \cdot \operatorname{frobChar}\left(mu, tau\right))), \operatorname{evTypes}\left(lam.\operatorname{parts}.\operatorname{toList}\right)\right)\right): \operatorname{Int}): \operatorname{Rat}))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.leftAverage` (`✓ std3`).

*Citation.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

The first expression in equation (6.1), page 12, sums the signed Ev character sum over all partitions with reciprocal centralizer weights. No restriction on repeated or mixed part sizes is imposed.

**Definition 1.3 (The rectangular-character average).**

$$\forall n \in \operatorname{Nat},\; \operatorname{rightAverage}\left(n\right) = \sum_{lam: \operatorname{Nat}.\operatorname{Partition}\left(n\right)} (\operatorname{weight}\left(lam\right) \cdot ((\operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{map}\left((\operatorname{fun}(tau: \operatorname{List}\left(\operatorname{Nat}\right)) \mapsto \operatorname{frobChar}\left(![n,n,0], tau\right)), \operatorname{evTypes}\left(lam.\operatorname{parts}.\operatorname{toList}\right)\right)\right): \operatorname{Int}): \operatorname{Rat}))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.rightAverage` (`✓ std3`).

*Citation.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

The middle expression in equation (6.1), page 12, averages the Ev sum of the rectangular character with the same weights.

**Definition 1.4 (Conjecture 6.1).**

$$(\operatorname{claim}) \Leftrightarrow (\forall n \in \operatorname{Nat},\; (1 \le n) \Rightarrow ((\operatorname{leftAverage}\left(n\right) = \operatorname{rightAverage}\left(n\right)) \land (\operatorname{rightAverage}\left(n\right) = \operatorname{ite}\left(\operatorname{Even}\left(n\right), ((\operatorname{Nat}.\operatorname{choose}\left((\operatorname{Nat}.\operatorname{div}\left(n, 2\right)+2), 2\right): \operatorname{Nat}): \operatorname{Rat}), (0: \operatorname{Rat})\right))))$$

*Formalization.* `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.claim` (`✓ std3`).

*Citation.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

Conjecture 6.1, equation (6.1), page 12 (journal Conjecture 17, page 15), states: “For any integer n≥1,”. The displayed proposition encodes both equalities of (6.1). The domain is n : Nat with 1 ≤ n. Ev retains each independent replacement, including repeated cycle types; R3 pads even partitions by zeros, and ![n,n,0] pads the rectangle. Character sums are integers cast to Rat. Nat.div denotes integer division, so Nat.div n 2 equals the source’s n/2 on the even branch. The inherited frobChar is the Frobenius coefficient model; its representation-theoretic interpretation is the literature input of Lemma 3.1.

**Theorem 1.5 (The weighted identity and closed form).**

$$\forall n \in \operatorname{Nat},\; (1 \le n) \Rightarrow ((\operatorname{leftAverage}\left(n\right) = \operatorname{rightAverage}\left(n\right)) \land (\operatorname{rightAverage}\left(n\right) = \operatorname{ite}\left(\operatorname{Even}\left(n\right), ((\operatorname{Nat}.\operatorname{choose}\left((\operatorname{Nat}.\operatorname{div}\left(n, 2\right)+2), 2\right): \operatorname{Nat}): \operatorname{Rat}), (0: \operatorname{Rat})\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hemmer, David J.; Straub, Armin; Westrem, Karlee J. (2025). *New identities in the character table of symmetric groups involving Riordan numbers*. DOI: [10.37236/14401](https://doi.org/10.37236/14401). URL: <https://arxiv.org/abs/2509.02796v1>.

*Commentary.*

The per-partition equality gives the equality of averages. Removing a marked part of size k multiplies the centralizer factor by k times its new multiplicity, which gives the cycle-index recurrence over any commutative Rat-algebra. Coefficient induction determines the solution of its first-order formal differential equation. For part input 2 times (z^k+1+z^(−k)), the solution is the product of the squares of three geometric series. Subtracting the adjacent Laurent coefficient cancels the (1−t)^2 factor and leaves (1−t²)^(−3). Its even coefficients are the stated binomial values, and its odd coefficients vanish.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.claim`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.leftAverage`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.result`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.rightAverage`
- Truth anchor: `D5/S3/Combinatorics/Partitions/HemmerStraubWestremWeightedAverage.weight`
- Dependency: [D5/S3/Combinatorics/Partitions/HemmerStraubWestrem](HemmerStraubWestrem.md)
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2](../PerfectMatchings/DeformedJucysMurphyC2.md)
