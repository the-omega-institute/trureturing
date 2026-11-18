# Injective selection of prime subsets

## Abstract

Injective selection of prime subsets.

**Theorem 1.1 (Prime bin counting).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.multibox_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.multibox_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite index type, pairwise disjoint finite prime bins P(j), prescribed natural cardinalities k(j), positive real bounds B(j), real lambda and positive cutoff x, suppose every prime in P(j) is at most B(j), the sum of k(j) exceeds the distinct-prime threshold, and the sum of k(j)*log(B(j)) is at most log(x). Then the product of choose(card(P(j)),k(j)) is at most tailCount(lambda,x). There is no capacity assumption: an impossible selection has binomial coefficient zero. Unique prime factorization makes products of different prime subsets distinct. Disjointness recovers each component from its union. Each selected product is positive, has exactly the sum of k(j) distinct prime factors, and fits below x by its logarithmic cost.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.multibox_bound`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTailUpper](../OmegaTailUpper.md)
