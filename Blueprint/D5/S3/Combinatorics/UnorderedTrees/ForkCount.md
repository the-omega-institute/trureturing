# Counting normalized fork decorations

## Abstract

Two bounded binomial sums give the actual unordered rooted-tree count.

**Definition 1.1 (Weak compositions with a base weight).**

$$\forall n \in \mathbb{N}, base \in \mathbb{N}, k \in \mathbb{N},\; \left(\operatorname{Slots}\left(n, base, k\right) = \{f: \operatorname{Fin}\left(k\right) \to \mathbb{N} \mid base+\sum_{i \in \operatorname{Fin}\left(k\right)} \operatorname{f}\left(i\right) = n\}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkCount.Slots` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every slot contributes a nonnegative leaf count to the prescribed total weight.

**Definition 1.2 (Equal-arm slots).**

$$\forall n \in \mathbb{N},\; \left(\operatorname{Equal}\left(n\right) = \Sigma b: \operatorname{Fin}\left(n+1\right), \Sigma m: \operatorname{Fin}\left(n+1\right), \operatorname{Slots}\left(n, b.val+5+2m.val, b.val+2\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkCount.Equal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The b+1 spine multiplicities and the difference of the two tip offsets are the b+2 slots. The smaller tip offset m contributes twice to the base weight.

**Definition 1.3 (Unequal-arm slots).**

$$\forall n \in \mathbb{N},\; \left(\operatorname{Unequal}\left(n\right) = \Sigma b: \operatorname{Fin}\left(n+1\right), \Sigma c: \operatorname{Fin}\left(n+1\right), \{f: \operatorname{Slots}\left(n, b.val+c.val+5, b.val+c.val+3\right) \mid 0 < c.val\}\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkCount.Unequal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive c separates the arms. Both offsets contribute independently together with the b+c+1 spine multiplicities.

**Definition 1.4 (The two decoration families).**

$$\forall n \in \mathbb{N},\; \left(\operatorname{weightSplit}\left(n\right): \operatorname{Weighted}\left(n\right) \equiv \operatorname{Sum}\left(\operatorname{Equal}\left(n\right), \operatorname{Unequal}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/UnorderedTrees/ForkCount.weightSplit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For c=0 the two sorted tip offsets have the unique form (m,m+d), including d=0. For c>0 the two offsets are stored as separate slots. Decoding restores the original normalized decoration and its weight.

**Theorem 1.5 (The equal-arm and unequal-arm contributions).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = \sum_{b,m : \mathbb{N} \mid b+5+2m \le n} \operatorname{choose}\left(n-4-2m, b+1\right) + \sum_{1 \le u \le n-5} u \operatorname{choose}\left(n-3, u+2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/UnorderedTrees/ForkCount.count_by_arms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All sum indices are natural numbers. The equal-arm summand uses the b+2 slots after subtracting the base weight. For unequal arms put u=b+c. There are u decompositions with c positive and u+3 free slots. The Lean sum uses v=u−1, and the displayed reindexing covers precisely the same feasible values, including empty ranges.

## References

- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkCount.Equal`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkCount.Slots`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkCount.Unequal`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkCount.count_by_arms`
- Truth anchor: `D5/S3/Combinatorics/UnorderedTrees/ForkCount.weightSplit`
- Dependency: [D5/S3/Combinatorics/UnorderedTrees/ForkDecoration](ForkDecoration.md)
