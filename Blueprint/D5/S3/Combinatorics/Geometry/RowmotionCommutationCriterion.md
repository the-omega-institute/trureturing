# A complete criterion for commuting interval-closed toggles

## Abstract

The complete commutation relation of guarded interval-closed toggles on arbitrary partial orders.

Let P be any partially ordered set. A subset S is order-convex when it contains every point between each pair of its members. The operation toggle(x,S) changes membership at x precisely when the resulting set is order-convex, and otherwise retains S. The criterion concerns equality of both compositions on every order-convex starting set. It uses this original guarded operation at both stages.

**Theorem 1.1 (Complete commutation criterion).**

$$\forall P \in Type,\; [\operatorname{PartialOrder}\left(P\right)], \forall x \in P,\; \forall y \in P,\; (\forall S \in \operatorname{Set}\left(P\right),\; (\operatorname{OrdConnected}\left(S\right)) \Rightarrow (\operatorname{toggle}\left(x, \operatorname{toggle}\left(y, S\right)\right) = \operatorname{toggle}\left(y, \operatorname{toggle}\left(x, S\right)\right))) \Leftrightarrow ((x = y) \lor (((\neg (x \le y)) \land (\neg (y \le x))) \lor (((\operatorname{IsMin}\left(x\right)) \land ((\operatorname{IsMax}\left(y\right)) \land (\operatorname{CovBy}\left(x, y\right)))) \lor ((\operatorname{IsMin}\left(y\right)) \land ((\operatorname{IsMax}\left(x\right)) \land (\operatorname{CovBy}\left(y, x\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/RowmotionCommutationCriterion.toggles_commute_iff` (`✓ std3`). ∎

*Citation.* Jessica Striker (2018). *Rowmotion and generalized toggle groups*. DOI: [10.23638/dmtcs-20-1-17](https://doi.org/10.23638/dmtcs-20-1-17). URL: <https://arxiv.org/abs/1601.03710v5>.

*Commentary.*

For distinct points in a finite partially ordered set, Striker's Lemma 3.17 gives the criterion: the points are incomparable, or one covers the other and the lower point is minimal while the upper point is maximal. The Lean theorem includes equal points explicitly and proves the same characterization for arbitrary partial orders, without finiteness or local finiteness.

For sufficiency at an extremal covering pair x below y, compare two order-convex sets that agree away from y. Legality of flipping x transfers between them. When an interval after the flip has x as its lower endpoint and y as its upper endpoint, the covering condition leaves only those endpoints. In the remaining intervals involving x, maximality of y permits transfer of all required memberships. If the interval does not involve x, its membership follows from convexity of the starting set and minimality of x. Applying this transfer to S and toggle(y,S) shows that toggling y preserves the guard for x; order duality supplies the other guard. The two guarded compositions then agree in all four combinations of guard values. This argument does not assert that either flip is always legal. The incomparable case directly reuses incomparable_toggles_commute.

For necessity, suppose x is strictly below y. If a point lies strictly between them, toggling the empty set in the two orders leaves different singletons, because the two-point set is not order-convex. Thus x must be covered by y. If z is strictly below x, start with S consisting of all points strictly below y. Removing x gives an order-convex set T: a point above x and strictly below y would contradict the cover. Adding y instead gives the closed lower interval through y. The two further flips are both blocked by the missing point x between z and y. The compositions therefore give T and that closed lower interval, distinguished by membership at y. This proves minimality of x without choosing a covered predecessor. Order duality proves maximality of y.

The criterion gives the commutation relation needed when organizing compositions of the existing interval-closed toggles. It does not prove a rowmotion orbit formula, a return-period count, or a homomesy statement.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/RowmotionCommutationCriterion.toggles_commute_iff`
- Dependency: [D5/S3/Combinatorics/Geometry/RowmotionIncomparableToggles](RowmotionIncomparableToggles.md)
