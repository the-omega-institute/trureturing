# Weighted First-Return Towers

## Abstract

Constructive first-return towers recover all orbit lengths, including untouched and singleton cycles.

Let X be any finite type, f a permutation, S a marked subset, and R actual first-return data. The data contain a permutation H of S and positive lengths l(x), with f^l(x)(x)=H(x) and no intermediate positive iterate in S. Put T_x(0)=0 and T_x(n+1)=T_x(n)+l(H^n(x)). Untouched points are those in cycles disjoint from S. The tower model is the disjoint union of those points with pairs (x,k), where x is marked and 0<=k<l(x). Its explicit successor preserves the original step on untouched points, increments k below the roof, and sends (x,l(x)-1) to (H(x),0).

**Theorem 1.1 (Each Time Has One Completed-Return Count and Offset).**

$$\forall X \in FiniteType,\; \forall f \in \operatorname{Perm}\left(X\right),\; \forall S \in \operatorname{Set}\left(X\right),\; \forall R \in \operatorname{FirstReturnData}\left(f, S\right),\; \forall x \in S,\; \forall k \in Natural,\; \exists p \in \operatorname{Product}\left(Natural, Natural\right),\; \left(k = \operatorname{Elapsed}\left(R, x, \operatorname{First}\left(p\right)\right) + \operatorname{Second}\left(p\right) \land \left(\operatorname{Second}\left(p\right) < \operatorname{Length}\left(R, \operatorname{NextIterate}\left(R, \operatorname{First}\left(p\right), x\right)\right) \land \operatorname{Iterate}\left(f, k, x\right) = \operatorname{Iterate}\left(f, \operatorname{Second}\left(p\right), \operatorname{NextIterate}\left(R, \operatorname{First}\left(p\right), x\right)\right)\right)\right) \land \left(\forall t \in \operatorname{Product}\left(Natural, Natural\right),\; \left(k = \operatorname{Elapsed}\left(R, x, \operatorname{First}\left(t\right)\right) + \operatorname{Second}\left(t\right) \land \left(\operatorname{Second}\left(t\right) < \operatorname{Length}\left(R, \operatorname{NextIterate}\left(R, \operatorname{First}\left(t\right), x\right)\right) \land \operatorname{Iterate}\left(f, k, x\right) = \operatorname{Iterate}\left(f, \operatorname{Second}\left(t\right), \operatorname{NextIterate}\left(R, \operatorname{First}\left(t\right), x\right)\right)\right)\right) \Rightarrow t = p\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.temporal_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural time k there is exactly one pair (n,d) with k=T_x(n)+d and 0<=d<l(H^n(x)); its position is f^k(x)=f^d(H^n(x)). Strict increase of cumulative return times makes the half-open return intervals disjoint. Thus n records the full elapsed history even after an induced cycle repeats. Uniqueness of this temporal pair and uniqueness of the spatial tower coordinate both hold.

**Theorem 1.2 (Every Original Point Has One Tower Coordinate).**

$$\forall X \in FiniteType,\; \forall f \in \operatorname{Perm}\left(X\right),\; \forall S \in \operatorname{Set}\left(X\right),\; \forall R \in \operatorname{FirstReturnData}\left(f, S\right),\; \operatorname{ConstructedTowerEquivalence}\left(R, f\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.tower_decomposition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The encoding sends an untouched point to itself and (x,k) to f^k(x). First-visit minimality proves that different segments cannot overlap. A greedy decomposition of every natural iterate into complete return segments and one interior offset proves surjectivity. The encoding intertwines the explicit tower successor with f. No orbit partition is assumed.

**Theorem 1.3 (Least Period Is the Sum of Actual Segment Lengths).**

$$\forall X \in FiniteType,\; \forall f \in \operatorname{Perm}\left(X\right),\; \forall S \in \operatorname{Set}\left(X\right),\; \forall R \in \operatorname{FirstReturnData}\left(f, S\right),\; \forall x \in S,\; \forall N \in Natural,\; \operatorname{LeastPositivePeriod}\left(\operatorname{Next}\left(R\right), x, N\right) \Rightarrow \operatorname{LeastPositivePeriod}\left(f, x, \operatorname{Elapsed}\left(R, x, N\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.least_period_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cumulative return time T_x(N) returns to x. If a shorter positive original time returned to x, its greedy interior offset would have to be zero by first-visit minimality. The remaining induced return count would contradict the least positive H-period. This proves minimality, not just existence of a return.

Write p_f(z) for the least positive f-period, including period one. Write L(x)=sum_{i<p_H(x)} l(H^i(x)). The full cycle inventory is the rational polynomial I_f(Z)=sum_z Z^p_f(z)/p_f(z). Each cycle contributes exactly one monomial, including fixed points. This is an additive encoding of the complete cycle multiset, not the conventional multiplicative cycle-index polynomial.

**Theorem 1.4 (Every Additive Orbit-Length Statistic).**

$$\forall X \in FiniteType,\; \forall f \in \operatorname{Perm}\left(X\right),\; \forall S \in \operatorname{Set}\left(X\right),\; \forall R \in \operatorname{FirstReturnData}\left(f, S\right),\; \forall A \in AdditiveCommutativeMonoid,\; \forall Phi \in \operatorname{Function}\left(Natural, A\right),\; \operatorname{RootSum}\left(f, Phi\right) = \operatorname{Add}\left(\operatorname{UntouchedRootSum}\left(R, Phi\right), \operatorname{WeightedEndpointSum}\left(R, Phi\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.weighted_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every additive observable Phi, sum_z Phi(p_f(z)) equals the untouched-root sum plus sum_x l(x) times Phi(L(x)). The constructive tower bijection supplies the change of variables, and the least-period theorem supplies the weight of each tower. Taking length indicators recovers every root multiplicity.

**Theorem 1.5 (The Complete Weighted Cycle Inventory).**

$$\forall X \in FiniteType,\; \forall f \in \operatorname{Perm}\left(X\right),\; \forall S \in \operatorname{Set}\left(X\right),\; \forall R \in \operatorname{FirstReturnData}\left(f, S\right),\; \operatorname{CycleInventory}\left(f\right) = \operatorname{Add}\left(\operatorname{UntouchedInventory}\left(R\right), \operatorname{WeightedInventory}\left(R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.weighted_cycle_inventory` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Apply the preceding inventory theorem to Phi(n)=Z^n/n over rational polynomials. The marked contribution is sum_x l(x) Z^L(x)/L(x), and the untouched contribution remains explicit. The reciprocal is always defined at a positive period. Empty marked sets and singleton original cycles remain in scope.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.least_period_sum`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.temporal_decomposition`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.tower_decomposition`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.weighted_cycle_inventory`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/FiniteReturnTowers.weighted_inventory`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteEndpointPairing](FiniteEndpointPairing.md)
