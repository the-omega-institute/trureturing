# DendriteObstruction - StandardDendroid

## Abstract

Standard dendroid geometry from arcwise connectedness and hereditary unicoherence.

**Theorem 1.1 (Subcontinua contain their joining arcs).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.arc_convex`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.arc_convex` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a compact metric carrier, StandardDendroid states actual arcwise connectedness and hereditary unicoherence: the intersection of any two compact connected subsets is preconnected, including the empty case. The definition contains no dynamical, uniform packing or co-connected-opening field. Arcwise connectedness uses actual continuous injective parameterizations of the closed unit interval with prescribed distinct endpoints.

A compact connected subset containing the two endpoints of any embedded arc contains the whole arc. Hereditary unicoherence makes its intersection with the arc preconnected. Pulling back through the compact interval embedding gives a preconnected subset of the real interval containing both endpoints, hence the entire interval. EmbeddedArc.between_subset proves the order statement for arbitrary two parameters.

**Theorem 1.2 (The accepted history hull premise).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.staticArcHull`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.staticArcHull` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The standard arcwise connected and hereditarily unicoherent geometry supplies StaticArcHull: choose an arc between distinct endpoints and apply arc_convex to every compact connected set containing the endpoints. This is a direct consumed interface to CompactHistories, with no additional geometric assumption.

**Theorem 1.3 (Uniqueness of the arc carrier).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.arc_unique`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.arc_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any two embedded arcs with the same ordered endpoints have equal carriers, by applying arc_convex in both directions. This carrier uniqueness is consumed in the no-circle proof. It does not assert uniqueness of parameterization.

**Theorem 1.4 (No embedded circle).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.no_circle`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.no_circle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every continuous map from AddCircle (1 : Real) to a standard dendroid fails to be injective. Under a hypothetical injection, the two oppositely parameterized semicircles give two embedded arcs with the same endpoints. Carrier uniqueness forces the first semicircle quarter point into the second semicircle, contradicting the actual AddCircle quotient coordinates.

**Theorem 1.5 (The standard structure on a subcontinuum).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.subcontinuum`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.subcontinuum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every compact connected subset of a standard dendroid inherits StandardDendroid on its actual subtype. Arc convexity places the ambient joining arc inside the subset, and continuous interval extension gives an actual subtype-valued embedded arc. Compact connected subtype sets map to ambient subcontinua; the injective subtype inclusion preserves their intersection and reflects preconnectedness. Thus the least continuum hull in the dynamic proof is again a standard dendroid.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.arc_convex`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.arc_unique`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.no_circle`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.staticArcHull`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/StandardDendroid.subcontinuum`
- Dependency: [D5/S1/Dynamics/Shadowing/DendriteObstruction/CompactHistories](CompactHistories.md)
