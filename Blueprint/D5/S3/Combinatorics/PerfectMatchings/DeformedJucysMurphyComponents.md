# Complete Components and Rotation Coordinates

## Abstract

Complete native components supply the live rotation coordinates used in the cut counts.

**Theorem 1.1 (A Rotation Orbit Has the Component's Identity-Edge Count).**

$$\forall k \in Nat,\; \forall p \in \operatorname{P}\left(k\right),\; \forall x \in \operatorname{Fin}\left(\operatorname{Twice}\left(k\right)\right),\; \operatorname{OrbitCard}\left(p, x\right) = \operatorname{ComponentEdgeCard}\left(p, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyComponents.rotation_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Rotation is matchingPerm(p)*matchingPerm(e(k)). OrbitCard counts the full SameCycle orbit of x. ComponentEdgeCard counts the literal identity edges in x's component. The orbit-to-edge bijection is used by the actual rotation cut proof; doubled edges and singleton orbits remain in scope.

The full product-rotation orbit-size multiset is two copies of the complete coset-type multiset, including parts of size one. This is a reused consequence of the frozen InvolutionOrbitSplit.component_split and component_orbit_classes: each component consists of two nonempty disjoint rotation orbits, exchanged by the identity matching, and each orbit contains exactly one endpoint of every identity edge. Thus a component with r edges contributes two orbits of size r; a doubled edge contributes two fixed points. This source correspondence is recorded without a separate new multiset theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyComponents.rotation_card`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/FiniteBandSwitch](FiniteBandSwitch.md)
