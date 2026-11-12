# DendriteObstruction - Arc geometry

## Abstract

Concrete compact hyperspace geometry for the persistence argument.

**Theorem 1.1 (Continuous diameter).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry.continuous_compact_diam`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry.continuous_compact_diam` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every metric space X, diameter is a continuous real-valued function on the Vietoris space of nonempty compact subsets of X. The continuous hyperspace product K times K and the upper Vietoris conditions for the closed and open distance sublevel sets prove the two semicontinuity directions. Compactness makes the maximum pairwise distance attained, so the strict sublevel condition controls the actual diameter.

**Theorem 1.2 (Compact family of large subcontinua).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry.compact_continua_ge`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry.compact_continua_ge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a compact metric X and any real a, the nonempty compact connected subsets K with diameter at least a form a compact subset of NonemptyCompacts X. The connected members form a closed set: a disconnected compact limit admits a disjoint closed separation and therefore disjoint open neighborhoods, and the corresponding Vietoris neighborhood excludes every connected compactum. Intersecting this closed family with the closed diameter superlevel set gives the claimed compactness. These are purely static hyperspace facts consumed by CompactHistories; no recurrence or persistence is assumed.

**Theorem 1.3 (Macroscopic continua in a closed set).**

Lean statement: `D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry.compact_continua_ge_in`

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry.compact_continua_ge_in` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a compact metric X, real a and closed subset Y, the family of nonempty compact connected K contained in Y with diameter at least a is compact. Closed containment in the actual Vietoris hyperspace is intersected with compact_continua_ge. This is the family used to retain a macroscopic continuum under descending intersections of invariant compacta.

## References

- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry.compact_continua_ge`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry.compact_continua_ge_in`
- Truth anchor: `D5/S1/Dynamics/Shadowing/DendriteObstruction/ArcGeometry.continuous_compact_diam`
