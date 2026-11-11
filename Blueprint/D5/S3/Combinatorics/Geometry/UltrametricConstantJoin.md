# Constant cross-distance joins of ultrametric spaces

## Abstract

Constant cross-distance joins preserve ultrametricity and give exact sphere, order and distance-center formulas.

Let X be an arbitrary indexed family of metric spaces, each with the ultrametric distance mixin. Fix a positive real cross-distance a and a proof hb that every component distance is at most a. Write J for Join X a ha hb. Indices and components may be empty; finiteness is imposed only for the finite sum and top-sphere count formulas. The center is the existing distance-center predicate from `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.center`. A radius is central when it is nonnegative and has a distance witness at every point.

**Theorem 1.1 (Non-strict component bounds suffice for the join metric).**

$$\operatorname{crossDist}\left(X, a, p, r\right) \leq \operatorname{max}\left(\operatorname{crossDist}\left(X, a, p, q\right), \operatorname{crossDist}\left(X, a, q, r\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.crossDist_triangle_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all three points of the dependent disjoint union, the displayed strong triangle inequality holds under the component upper bound. The cross-distance retains the old distance within a component and equals a between different components. The explicit metricSpace definition installs this metric on the dependent union; joinMetric transports it to Join without introducing a competing global metric on Sigma.

The resulting Mathlib ultrametric mixin is `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.isUltrametricDist`. The same-component and cross-component formulas are `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.dist_same` and `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.dist_cross`.

**Theorem 1.2 (Every sphere away from the join radius stays in its component).**

$$\operatorname{sphere}\left(\langle i,x \rangle, t\right) = \operatorname{image}\left(inclusion, \operatorname{sphere}\left(x, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.sphere_eq_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every index i, point x in X i and real radius t different from a, the inclusion sends the old sphere onto the entire join sphere. No inequality between t and a is required. The corresponding existential witness equivalence is `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.sphere_witness_iff`.

**Theorem 1.3 (Strict bounds identify the sphere at the join radius).**

$$\operatorname{sphere}\left(p, a\right) = \{q \mid \operatorname{fst}\left(q\right) \neq \operatorname{fst}\left(p\right)\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.sphere_top` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume additionally that every component distance is strictly less than a. For every point p of J, its sphere at a consists exactly of the points in different components. This strict hypothesis is additional to the non-strict bound used to construct the metric.

**Theorem 1.4 (Every sphere count away from the join radius is preserved).**

$$\operatorname{card}\left(\operatorname{sphere}\left(\langle i,x \rangle, t\right)\right) = \operatorname{card}\left(\operatorname{sphere}\left(x, t\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.sphere_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every i, x in X i and real t different from a, Nat.card gives the displayed equality. This statement needs no finiteness assumption; the sphere inclusion is injective and surjective onto the sphere.

**Theorem 1.5 (The order of a finite join is the sum of the component orders).**

$$\operatorname{card}\left(J\right) = \sum_{i} \operatorname{card}\left(\operatorname{X}\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.card_join_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here the index type has a Fintype instance and every component is finite. The sum runs over that index type. The equivalence with the dependent disjoint union is equivSigma, and the general Nat.card equality is `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.card_join`.

**Theorem 1.6 (The top sphere contains all points outside the component).**

$$\operatorname{card}\left(\operatorname{sphere}\left(\langle i,x \rangle, a\right)\right) = \operatorname{card}\left(J\right) - \operatorname{card}\left(\operatorname{X}\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.sphere_top_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume a finite index type, finite components, and the strict component-distance bound. For every i and x in X i the displayed subtraction is natural-number subtraction, exactly as in Nat.card. No nonemptiness assumption on other components is hidden in the formula.

**Theorem 1.7 (Central radii away from the join radius are common component radii).**

$$t \in \operatorname{center}\left(J\right) \iff 0 \leq t \land \forall i, t \in \operatorname{center}\left(\operatorname{X}\left(i\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.mem_center_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real t different from a, the equivalence holds under the original non-strict component bound. The separate nonnegativity condition is retained, including when the index type is empty.

**Theorem 1.8 (The join radius is central exactly when each occupied component has another occupied component).**

$$a \in \operatorname{center}\left(J\right) \iff \forall i, \forall x:\operatorname{X}\left(i\right), \exists j, \operatorname{Nonempty}\left(\operatorname{X}\left(j\right)\right) \land j \neq i$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.top_mem_center_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The strict component-distance bound is assumed. The implication from an element of X i retains the vacuous empty-component cases. In particular the formula also applies to an empty join or to a join with a single index; it does not silently require two occupied components.

**Theorem 1.9 (The exact distance center separates the join radius from the other radii).**

$$\operatorname{center}\left(J\right) = \{t \mid 0 \leq t \land t \neq a \land \forall i, t \in \operatorname{center}\left(\operatorname{X}\left(i\right)\right)\} \cup \{t \mid t = a \land \forall i, \forall x:\operatorname{X}\left(i\right), \exists j, \operatorname{Nonempty}\left(\operatorname{X}\left(j\right)\right) \land j \neq i\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.center_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under strict component-distance bounds, this set equality combines the two preceding equivalences. It uses the original distance center and keeps every empty-index and empty-component case. The prescribed-count construction uses this formula at the outer join and the componentwise equivalence mem_center_iff at the inner joins.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges.center`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.card_join`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.card_join_sum`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.center_eq`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.crossDist_triangle_max`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.dist_cross`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.dist_same`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.isUltrametricDist`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.mem_center_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.sphere_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.sphere_eq_image`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.sphere_top`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.sphere_top_card`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.sphere_witness_iff`
- Truth anchor: `D5/S3/Combinatorics/Geometry/UltrametricConstantJoin.top_mem_center_iff`
- Dependency: [D5/S3/Combinatorics/Geometry/DovgosheyRovenskaCentralEdges](DovgosheyRovenskaCentralEdges.md)
