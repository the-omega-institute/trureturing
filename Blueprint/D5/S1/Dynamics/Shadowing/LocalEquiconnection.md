# Explicit Sphere Local Equiconnections

## Abstract

Normalized nonantipodal chords provide coherent local equiconnections on normed unit spheres and transport through homeomorphisms.

**Definition 1.1 (Normalized straight interpolation).**

$$\forall V: RealNormedSpace, \operatorname{sphere}(V) = \operatorname{LocalConnectorData}(\operatorname{NonantipodalPairs}(\operatorname{UnitSphere}(V)), (p,q,s) \mapsto \operatorname{normalize}((1-s)p+sq))$$

*Formalization.* `D5/S1/Dynamics/Shadowing/LocalEquiconnection.sphere` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the subtype sphere of radius one in any real normed space, use the open domain of pairs (p,q) with q≠-p. The connector normalizes (1-s)p+sq for s in [0,1]. Unit norms show that a zero chord would force s=1/2 and q=-p, so normalization is continuous throughout the stated domain. It has both endpoint identities and fixes every diagonal pair for every parameter. Finite dimensionality is unnecessary for this connector data.

**Definition 1.2 (Transport the domain and connector together).**

$$\forall X: TopologicalSpace, \forall Y: TopologicalSpace, \forall e: \operatorname{Homeomorphism}(X, Y), \forall H: \operatorname{LocalEquiconnection}(Y), \operatorname{transport}(e, H) = \operatorname{LocalConnectorData}(\operatorname{PairDomainPullback}(e, H), (p,q,s) \mapsto \operatorname{inverse}(e, \operatorname{connect}(H, \operatorname{e}(p), \operatorname{e}(q), s)))$$

*Formalization.* `D5/S1/Dynamics/Shadowing/LocalEquiconnection.transport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A homeomorphism e:X→Y pulls back the open pair domain and sends the connector output through e inverse. The continuity and all three identities are transported as data. Applying this to a homeomorphism onto a Euclidean unit sphere supplies genuine topological-sphere data without differentiability or any compatibility between e, the connector and the dynamical map. No compact LEC implies ANR assertion is made.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/LocalEquiconnection.sphere`
- Truth anchor: `D5/S1/Dynamics/Shadowing/LocalEquiconnection.transport`
- Dependency: [D5/S1/Dynamics/Shadowing/VerticalSuspensionSelector](VerticalSuspensionSelector.md)
