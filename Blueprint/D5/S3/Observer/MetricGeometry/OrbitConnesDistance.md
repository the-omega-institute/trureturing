# Observable-Supremum Distance on the Integer Orbit

## Abstract

Bounded observables with unit one-step update defect recover the exact distance on the free integer shift orbit.

**Theorem 1.1 (Admissible observables have unit one-step update defect).**

$$\forall f \in B_{L},\ \forall k \in \mathbb{Z},\ \Vert f(k+1)- f(k)\Vert \leq 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/OrbitConnesDistance.orbitLipBall_unit_update_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the admissible ball consist of bounded real functions on the integer orbit whose complexified observable has frozen read-update defect norm at most one at every coordinate. Evaluating that defect at the successor coordinate gives an adjacent real value change of at most one. Telescoping those adjacent bounds later supplies the global Lipschitz estimate used by the distance theorem.

**Theorem 1.2 (The observable supremum equals the integer orbit distance).**

$$\forall m, n \in \mathbb{Z},\ d_{L}(m, n) = \Vert m- n\Vert.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/OrbitConnesDistance.orbit_connes_distance_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Define the distance between two integer orbit points as the real supremum of their value gaps over bounded observables in the unit update-defect ball. Every such gap is at most the ambient integer distance by telescoping adjacent defects in either orbit orientation. The reverse bound is attained by the bounded observable k mapped to the minimum of the distance from k to m and the distance from m to n. The theorem concerns the free integer shift orbit itself, so it retains the absolute-displacement formula without the wrap-around of a finite cyclic quotient. It establishes only the same-orbit metric clause. It does not construct a spectral triple, identify an operator commutator norm, or make bundle, phase-separation, or type-classification claims.

**Theorem 1.3 (Distance from the orbit origin is absolute displacement).**

$$\forall n \in \mathbb{Z},\ d_{L}(0, n) = \Vert n\Vert.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/OrbitConnesDistance.orbit_distance_from_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Specializing the exact distance theorem to the orbit origin converts the integer metric into the absolute value of the real cast of the integer displacement. Negative and positive shifts therefore have the same distance, while no periodic identification is imposed.

**Theorem 1.4 (A nonconstant admissible observable attains distance three).**

$$\exists f \in B_{L},\ f(0) \neq f(3) \land \Vert f(0)- f(3)\Vert = 3.$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/MetricGeometry/OrbitConnesDistance.orbit_distance_three_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The clipped distance observable based at zero and clipped at three is bounded, belongs to the unit update-defect ball, takes distinct values at zero and three, and has endpoint gap three. This explicit nonconstant witness rules out an empty ball, an all-constant ball, and an identically zero distance.

## References

- Truth anchor: `D5/S3/Observer/MetricGeometry/OrbitConnesDistance.orbitLipBall_unit_update_defect`
- Truth anchor: `D5/S3/Observer/MetricGeometry/OrbitConnesDistance.orbit_connes_distance_eq`
- Truth anchor: `D5/S3/Observer/MetricGeometry/OrbitConnesDistance.orbit_distance_from_zero`
- Truth anchor: `D5/S3/Observer/MetricGeometry/OrbitConnesDistance.orbit_distance_three_witness`
- Dependency: [D5/S3/Observer/ObserverMetric](../ObserverMetric.md)
