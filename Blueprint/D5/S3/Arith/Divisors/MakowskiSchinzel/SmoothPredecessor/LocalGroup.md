# Finite subgroups and certified prefixes

## Abstract

Finite subgroups and certified prefixes

**Theorem 1.1 (Rank domination of an arbitrary finite subset).**

$$\forall l \in \operatorname{List}\left(\mathbb{N}\right),\; \forall s \in \operatorname{Finset}\left(\mathbb{N}\right),\; \operatorname{PairwiseLe}\left(l\right) \Rightarrow \left(\left(\forall q \in \mathbb{N},\; q \in s \Rightarrow q \in l\right) \Rightarrow \operatorname{lowerProduct}\left(\operatorname{take}\left(\operatorname{card}\left(s\right), l\right)\right) \le \operatorname{lowerProduct}\left(\operatorname{sort}\left(s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/LocalGroup.finite_subgroup_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let qs be a nondecreasing list of natural numbers. Sorting any finite subset F of its values gives a list that dominates the equally long prefix of qs coordinatewise. The factors (q-1)/q increase on positive q; at q=0 the factor is zero, which also preserves the comparison. Thus the lowerProduct of the sorted F is at least that prefix product and its rounded fixed product divided by scale. The exact (q-1)/q factors retain zero at q=0. Repetitions in qs are allowed. Ordering and membership are needed: the prefix of [3,2] at length one has product 2/3, exceeding the product 1/2 over F={2}; the list [3] gives the same failure without membership.

**Theorem 1.2 (Every finite subgroup inherits a checked prefix).**

$$\forall T \in \operatorname{List}\left(\mathbb{N}\right),\; \forall tl \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right)\right),\; \forall z \in \operatorname{List}\left(\operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \operatorname{stepTable}\left(tl, T, \operatorname{initialState}\left(\right)\right) = \operatorname{some}\left(z\right) \Rightarrow \left(\forall t \in \operatorname{Pair}\left(\mathbb{N}, \operatorname{Pair}\left(\mathbb{N}, \mathbb{N}\right)\right),\; \forall i \in \mathbb{N},\; \forall p \in \mathbb{N},\; \operatorname{PairwiseLe}\left(\operatorname{groupValues}\left(i, T\right)\right) \Rightarrow \left(\operatorname{getElemOption}\left(\operatorname{oddPrimes}\left(\right), i\right) = \operatorname{some}\left(p\right) \Rightarrow \left(\operatorname{getElemOption}\left(tl, i\right) = \operatorname{some}\left(t\right) \Rightarrow \left(\forall s \in \operatorname{Finset}\left(\mathbb{N}\right),\; \left(\forall q \in \mathbb{N},\; q \in s \Rightarrow q \in \operatorname{groupValues}\left(i, T\right)\right) \Rightarrow \left(\left(\operatorname{card}\left(s\right) = \operatorname{length}\left(\operatorname{groupValues}\left(i, T\right)\right) \Rightarrow \left(\forall j \in \mathbb{N},\; \forall L \in \mathbb{N},\; \operatorname{getElemOption}\left(z, i\right) = \operatorname{some}\left(\operatorname{Pair}\left(j, L\right)\right) \Rightarrow \operatorname{prefixOk}\left(p, j, L, t\right) = \operatorname{true}\left(\right)\right)\right) \Rightarrow \left(\operatorname{prefixOk}\left(p, \operatorname{card}\left(s\right), \operatorname{fixedProduct}\left(\operatorname{scale}\left(\right), \operatorname{take}\left(\operatorname{card}\left(s\right), \operatorname{groupValues}\left(i, T\right)\right)\right), t\right) = \operatorname{true}\left(\right) \land \frac{\operatorname{fixedProduct}\left(\operatorname{scale}\left(\right), \operatorname{take}\left(\operatorname{card}\left(s\right), \operatorname{groupValues}\left(i, T\right)\right)\right)}{\operatorname{scale}\left(\right)} \le \operatorname{lowerProduct}\left(\operatorname{sort}\left(s\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/LocalGroup.table_group_prefix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary T, tail list tl, tail tuple t and final state z, assume groupValues(i,T) is nondecreasing and stepTable(tl,T,initialState)=some(z). Require the selected group to pass its terminal check only if card(F) equals its full length. At index i with oddPrimes[i]=some(p) and tl[i]=some(t), no order between different groups is needed. For every finite subset F of one such subsequence, the certificate supplies a prefix check at count card(F), with fixed product L. Rank domination makes L/scale a lower bound for the exact lowerProduct of sorted F. For positive q, the factor (q-1)/q equals 1-1/q. The terminal check covers the case in which F has the full group size. No entry validity or counting condition is required. The ordered input is needed for rank domination, the run checks proper prefixes, the final test checks the full prefix, and the two lookups identify the prime and the exact tail constant used by that group.

## References

- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/LocalGroup.finite_subgroup_bound`
- Truth anchor: `D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/LocalGroup.table_group_prefix_bound`
- Dependency: [D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/GroupState](GroupState.md)
