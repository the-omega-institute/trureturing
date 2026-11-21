# Additive comparison on constant blocks

## Abstract

Constant-block cost comparison for the guarded rule.

**Definition 1.1 (Schedule at a constant rate).**

$$\forall (a: \mathbb{R})(rs: List(Bool)), block(a, rs)=map(r\mapsto (a, r), rs)$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuyAdditive.block` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

Map each Boolean action to a pair of the fixed real rate and that action.

**Theorem 1.2 (One reset price of excess from zero rule carry).**

$$\forall (K a o: \mathbb{R})(s: State)(rs: List(Bool)), (0<K\land 0\le a\land 0\le o\land carry(s)=0\land acc(s)=0\land reset(K, s, a)=decide(crossing(K, s, a)))\Rightarrow policyCost(K, s, replicate(length(rs), a))\le comparatorCost(K, o, block(a, rs))+K$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuyAdditive.single_block_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

Start the rule with zero carry and rent accumulator, with the first action governed by the ordinary threshold. The comparator may start with any nonnegative carry. For positive rates, telescope the first-crossing and minimum-cost potentials from Schiavo's Proposition 6 and Lemmas 7–8. A zero-rate block with zero rule carry has zero rule cost.

**Theorem 1.3 (Two reset prices of excess over two constant blocks).**

$$\forall (K a b: \mathbb{R})(rs ss: List(Bool)), (0<K\land 0\le a\land 0\le b)\Rightarrow policyCost(K, initial, append(replicate(length(rs), a), replicate(length(ss), b)))\le comparatorCost(K, 0, append(block(a, rs), block(b, ss)))+2\cdot K$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuyAdditive.two_block_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

The two real rates are nonnegative and either action block can be empty. With an increase, the ordered-crossing polynomial estimate bounds the rule's change of potential. With a guarded decrease, reset at the drop and use the monotonicity of the comparator potential from Lemma 14. With a decrease before any crossing, compare costs through the first ordinary reset and apply the one-block bound to the remaining suffix. If no crossing occurs, the unfinished-cycle comparison suffices.

## References

- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuyAdditive.block`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuyAdditive.single_block_bound`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuyAdditive.two_block_bound`
- Dependency: [D5/S3/Analytic/Polynomial/OrderedCrossingGap](../../Analytic/Polynomial/OrderedCrossingGap.md)
- Dependency: [D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuy](GuardedRentOrBuy.md)
