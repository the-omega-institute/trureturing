# Counting the First Decorated Family

## Abstract

The decorated family has the binomial-product cardinality in the first avoidance formula.

**Theorem 1.1 (Counting when all required gaps fit).**

$$\forall n \in \mathrm{Nat}, m \in \mathrm{Nat}, k \in \mathrm{Nat},\; 1 \le m \Rightarrow \left(\operatorname{card}\left(\operatorname{upperSupport}\left(n, m\right)\right) - k \le m - 1 \Rightarrow \operatorname{card}\left(\operatorname{TwelveData}\left(n, m, k\right)\right) = \operatorname{choose}\left(n - m, k\right) \cdot \operatorname{numDerangements}\left(k\right) \cdot \operatorname{choose}\left(m + k - 1, n - m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveCard.card_twelveData_of_enough` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

When the number of mandatory positive gaps does not exceed m minus one, the decorated-data cardinality is choose(n minus m,k) times choose(m plus k minus one,n minus m) times the k-th derangement number.

**Theorem 1.2 (Counting every decorated fiber).**

$$\forall n \in \mathrm{Nat}, m \in \mathrm{Nat}, k \in \mathrm{Nat},\; 1 \le m \Rightarrow \operatorname{card}\left(\operatorname{TwelveData}\left(n, m, k\right)\right) = \operatorname{choose}\left(n - m, k\right) \cdot \operatorname{numDerangements}\left(k\right) \cdot \operatorname{choose}\left(m + k - 1, n - m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ArrowWilfTwelveCard.card_twelveData` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Robin D.P. Zhou, Xinyang Yu (2026). *Arrow-Wilf equivalences and enumerative results for short arrow patterns*. DOI: [10.48550/arXiv.2609.29392](https://doi.org/10.48550/arXiv.2609.29392). URL: <https://arxiv.org/abs/2609.29392v1>.

*Commentary.*

For every natural n,m,k with m positive, the same binomial-product formula counts TwelveData(n,m,k); when mandatory gaps cannot fit, both sides vanish.

## References

- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCard.card_twelveData`
- Truth anchor: `D5/S3/Combinatorics/ArrowWilfTwelveCard.card_twelveData_of_enough`
- Dependency: [D5/S3/Combinatorics/ArrowWilfTwelveCount](ArrowWilfTwelveCount.md)
