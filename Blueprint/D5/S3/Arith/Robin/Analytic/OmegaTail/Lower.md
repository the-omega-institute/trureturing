# Injective selection of prime subsets

## Abstract

Injective selection of prime subsets.

**Theorem 1.1 (Recover prime support from its product).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.prime_product_injective`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.prime_product_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two finite prime supports with equal products are equal. Taking prime factors recovers each support.

**Theorem 1.2 (Count distinct prime factors of a support product).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.omega_prime_product`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.omega_prime_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The number of distinct prime factors of a finite prime support's product is the cardinality of that support.

**Theorem 1.3 (Recover a selection from its disjoint bin).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.bin_union_inter`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.bin_union_inter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For selections from pairwise disjoint bins, intersect the union of the selections with a bin to recover that bin's selection.

**Theorem 1.4 (Prime bin counting).**

Lean statement: `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.multibox_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.multibox_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite index type, pairwise disjoint finite prime bins P(j), prescribed natural cardinalities k(j), positive real bounds B(j), real lambda and positive cutoff x, suppose every prime in P(j) is at most B(j), the sum of k(j) exceeds the distinct-prime threshold, and the sum of k(j)*log(B(j)) is at most log(x). Then the product of choose(card(P(j)),k(j)) is at most tailCount(lambda,x). There is no capacity assumption: an impossible selection has binomial coefficient zero. Unique prime factorization makes products of different prime subsets distinct. Disjointness recovers each component from its union. Each selected product is positive, has exactly the sum of k(j) distinct prime factors, and fits below x by its logarithmic cost.

## References

- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.bin_union_inter`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.multibox_bound`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.omega_prime_product`
- Truth anchor: `D5/S3/Arith/Robin/Analytic/OmegaTail/Lower.prime_product_injective`
- Dependency: [D5/S3/Arith/Robin/Analytic/OmegaTailUpper](../OmegaTailUpper.md)
