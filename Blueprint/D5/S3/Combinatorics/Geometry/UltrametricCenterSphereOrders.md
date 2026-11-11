# Complete classification of prescribed central sphere counts

## Abstract

A divisor recurrence gives exactly all orders of finite nonempty ultrametrics with prescribed central radii and pointwise sphere counts, including realizations for every prescribed pair in every gap.

The central-graph edge comparison is the separate result `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.result`. The classification below concerns pointwise sphere counts at every radius in the distance center.

The center throughout is the existing distance-center predicate `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.center`. It consists of the nonnegative radii attained from every point; witnesses may depend on the point. No replacement notion of center is used. The classification quantifies over arbitrary natural h and n, real-valued radii c on the naturals, and natural-valued counts b. The required initial radius and strict increases are $\operatorname{c}\left(0\right) = 0, \forall i < h, \operatorname{c}\left(i\right) < \operatorname{c}\left(i+1\right)$. When positivity of counts is assumed it means every index through h, including zero.

**Remark 1.1 (Nonempty finite sums with repetition).**

Lean statement: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.PositiveSum`

*Formalization.* `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.PositiveSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

PositiveSum A t means that there are a natural k and a list indexed by Fin (k + 1), all of whose entries belong to A, and whose sum is t. Repeated summands are allowed. This definition does not insert a zero-length sum.

**Definition 1.2 (The recursive candidate orders).**

$$\operatorname{orders}\left(b, 0\right) = \{1\}, \operatorname{orders}\left(b, i+1\right) = \{n \mid \exists t, \operatorname{PositiveSum}\left(\operatorname{orders}\left(b, i\right), t\right) \land t \mid \operatorname{b}\left(i+1\right) \land n = \operatorname{b}\left(i+1\right)+t\}$$

*Formalization.* `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.orders` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The divisibility symbol uses natural-number divisibility. These sets depend only on the count sequence. Their elements are positive by `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.orders_pos`. The recurrence itself is defined even without the positivity hypotheses later imposed by the existence classification.

**Theorem 1.3 (A positive count bounds every sum to be checked).**

$$n \in \operatorname{orders}\left(b, i+1\right) \iff \exists t, 0 < t \land t \leq \operatorname{b}\left(i+1\right) \land \operatorname{PositiveSum}\left(\operatorname{orders}\left(b, i\right), t\right) \land t \mid \operatorname{b}\left(i+1\right) \land n = \operatorname{b}\left(i+1\right)+t$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.mem_orders_succ_iff_bounded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary b, i and n, assume the count at i + 1 is positive. Then the recurrence is equivalent to the bounded search displayed here. This is a general bound on the recurrence, rather than an enumeration of a fixed example.

**Theorem 1.4 (Each prescribed closed ball has an order in the recurrence).**

$$\operatorname{card}\left(\operatorname{closedBall}\left(x, \operatorname{c}\left(h\right)\right)\right) \in \operatorname{orders}\left(b, h\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.closedBall_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let X be any finite metric space with IsUltrametricDist, and let x be any point of X. Assume the initial radius and strict increases stated above and that, at every prescribed radius through h, the sphere about every point has the prescribed count. Then the displayed membership holds. This theorem does not assume the center equality or positivity of b. Lower closed balls partition a strict upper ball by lower_closedBalls; closedBall_card_eq separates its sphere from its strict ball.

**Theorem 1.5 (Every realization has initial count one and an order in the recurrence).**

$$\operatorname{b}\left(0\right) = 1 \land \operatorname{card}\left(X\right) \in \operatorname{orders}\left(b, h\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.necessary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite nonempty ultrametric X, assume the initial radius and strict increases, center X exactly the image of c on the indices through h, and every prescribed pointwise sphere count. Then the displayed criterion holds. Necessity imposes no restriction on other distance values and does not separately assume positive counts. It includes h equal to zero: the finite nonempty space is then a singleton.

**Remark 1.6 (A realization retains the entire center, count and support contract).**

Lean statement: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.Model`

*Formalization.* `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.Model` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Model c b u v h n contains a carrier with MetricSpace, IsUltrametricDist, Finite and Nonempty instances; its Nat.card is n; its original distance center is exactly the prescribed radii through h; and every pointwise sphere count at every such radius equals b. Its distance field restricts all distances to allowed c u v h.

The allowed set is the union of the central radii through h and the values of u and v at indices strictly below h, as defined by `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.allowed`. For every gap these two auxiliary radii are fixed in advance and satisfy $\forall i < h, \operatorname{c}\left(i\right) < \operatorname{u}\left(i\right) < \operatorname{v}\left(i\right) < \operatorname{c}\left(i+1\right)$. The contract bounds the support; it does not require every allowed auxiliary value to occur.

**Theorem 1.7 (Every candidate order is realized for every prescribed pair in every gap).**

$$\operatorname{b}\left(0\right) = 1 \land n \in \operatorname{orders}\left(b, h\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{Model}\left(c, b, u, v, h, n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.sufficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the initial radius, strict increases, every prescribed gap inequality just stated, and positive counts through h. If the initial count is one and n belongs to orders b h, then Model c b u v h n is nonempty. The auxiliary sequences u and v are arbitrary subject to those inequalities. The construction begins at a singleton and forms groups of lower-level models; one group is joined at the first auxiliary radius, the other groups at the second, and the groups at the next central radius. This prevents either newly introduced auxiliary radius from becoming central.

**Theorem 1.8 (The exact criterion holds with arbitrary prescribed auxiliary pairs).**

$$\operatorname{Nonempty}\left(\operatorname{Model}\left(c, b, u, v, h, n\right)\right) \iff \operatorname{b}\left(0\right) = 1 \land n \in \operatorname{orders}\left(b, h\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.possible_orders_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the initial radius, strict increases, every prescribed gap inequality, and positive counts through h. For every n the displayed equivalence is exact. Model contains all the metric, finiteness, nonemptiness, order, original center, pointwise count and distance-support requirements; none is dropped. If b at zero differs from one, the right side is false and no such Model exists.

**Theorem 1.9 (The same recurrence classifies all realizations without a distance-support restriction).**

$$(\exists X:Type, \exists m:\operatorname{MetricSpace}\left(X\right), \operatorname{IsUltrametricDist}\left(X\right) \land \operatorname{Finite}\left(X\right) \land \operatorname{Nonempty}\left(X\right) \land \operatorname{card}\left(X\right) = n \land \operatorname{center}\left(X\right) = \operatorname{image}\left(c, \operatorname{Iic}\left(h\right)\right) \land \forall i \leq h, \forall x:X, \operatorname{card}\left(\operatorname{sphere}\left(x, \operatorname{c}\left(i\right)\right)\right) = \operatorname{b}\left(i\right)) \iff (\operatorname{b}\left(0\right) = 1 \land n \in \operatorname{orders}\left(b, h\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.possible_orders_unrestricted_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume only the initial radius, strict increases and positive counts through h. The left side existentially chooses a carrier and its metric; all other structures and sphere counts refer to that same chosen metric. There is no hypothesis restricting the remaining distances. The converse chooses one-third and two-thirds of each prescribed gap and applies the stronger construction. This is the unrestricted existence iff, including the initial-count obstruction and the singleton boundary.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.center`
- Truth anchor: `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.result`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.Model`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.PositiveSum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.allowed`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.closedBall_order`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.mem_orders_succ_iff_bounded`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.necessary`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.orders`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.orders_pos`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.possible_orders_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.possible_orders_unrestricted_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricCenterSphereOrders.sufficient`
- Dependency: [D5/S3/Combinatorics/Geometry/UltrametricConstantJoin](UltrametricConstantJoin.md)
