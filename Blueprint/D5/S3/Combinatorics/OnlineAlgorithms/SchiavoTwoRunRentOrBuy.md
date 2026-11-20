# Schiavo's two-run question for repeated rent-or-buy

## Abstract

One online rule with factor three and a two-run additive bound.

**Definition 1.1 (At most two constant runs).**

$$\forall (xs: List(\mathbb{R})), AtMostTwoRuns(xs)\Leftrightarrow \exists (a b: \mathbb{R})(m n: \mathbb{N}), xs=append(replicate(m, a), replicate(n, b))$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy.AtMostTwoRuns` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

The increment list is the concatenation of two lists, each a replication of a real rate for a natural number of entries. Empty blocks and equal rates are allowed.

**Definition 1.2 (Cost on the whole session).**

$$\forall (K: \mathbb{R})(xs: List(\mathbb{R}))(first: Bool)(rs: List(Bool)), sessionCost(K, xs, first, rs)=bill(K, 0, 0, first)+comparatorCost(K, 0, zip(xs, rs))$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy.sessionCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

Add the first-call bill, with zero history and no new increment, to the cost of the paired list from zero carry. A comparator has one freely chosen first action and one action per increment. The length hypothesis in the theorem pairs every increment.

**Definition 1.3 (Actions obtained from visible prefixes).**

$$\forall (rule: List(\mathbb{R})\Rightarrow Bool)(xs: List(\mathbb{R})), actions(rule, xs)=ofFn(i: Fin(length(xs))\mapsto rule(take(xs, i+1)))$$

*Formalization.* `D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy.actions` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

For each zero-based index i of the increment list, evaluate the rule on its first i+1 increments. The separate first action uses the empty list.

**Theorem 1.4 (One deterministic rule achieves both bounds).**

$$\exists (c: \mathbb{R}), 1\le c\land (\forall (K: \mathbb{R}), 0<K\Rightarrow \exists (rule: List(\mathbb{R})\Rightarrow Bool), \forall (xs: List(\mathbb{R})), (\forall (a: \mathbb{R}), a\in xs\Rightarrow 0\le a)\Rightarrow \forall (first: Bool)(rs: List(Bool)), length(rs)=length(xs)\Rightarrow (online(K, rule, xs)\le c\cdot sessionCost(K, xs, first, rs)\land (AtMostTwoRuns(xs)\Rightarrow online(K, rule, xs)\le sessionCost(K, xs, first, rs)+2\cdot K)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy.schiavo_section5b_third_question` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Vasco Schiavo (2026). *A Sharp Additive Bound for the Threshold Rule in Repeated Rent-or-Buy*. URL: <https://arxiv.org/abs/2611.06955v1>.

*Commentary.*

Schiavo asks on page 15, §5.B, “Can a rule lose at most 2K on two runs and also be c-competitive for some constant c?”

Write online(K, rule, xs) for sessionCost(K, xs, rule([]), actions(rule, xs)). Take c = 3. For every positive real reset price K, choose the guarded prefix rule once. On every finite list of nonnegative real increments, and against every comparator schedule of the same horizon, its cost is at most three times the comparator cost. If the increment list has at most two runs, its cost is also at most the comparator cost plus 2K.

The list has length T−1. Call t observes the first t−1 entries, and every call, including the final call and each reset call, pays the full incoming history as rent. Both inequalities hold for the same deterministic rule. The arbitrary comparator includes any minimum-cost schedule.

The replayed decisions agree with the evaluations on visible prefixes. The competitive inequality follows from cycle accounting, and the additive inequality follows from the two constant-block comparison. The empty increment list represents a one-call session.

## References

- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy.AtMostTwoRuns`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy.actions`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy.schiavo_section5b_third_question`
- Truth anchor: `D5/S3/Combinatorics/OnlineAlgorithms/SchiavoTwoRunRentOrBuy.sessionCost`
- Dependency: [D5/S3/Combinatorics/OnlineAlgorithms/GuardedRentOrBuyAdditive](GuardedRentOrBuyAdditive.md)
