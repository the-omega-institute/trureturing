# Stationing Counts

## Abstract

Record exact support and occupancy counts for labeled Boolean stationings.

This module counts labeled Boolean stationings and their occupied supports. It does not assert that arithmetic orbits exhaust this Boolean model, and it does not close a finite certificate, measured exponent, density, or asymptotic law.

**Theorem 1.1 (All labeled stationings have power-of-two cardinality).**

$\forall n\in\mathbb{N},\ \operatorname{card}(\operatorname{Stationing}(n))=2^n$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/StationingCombinatorics.stationing_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each labeled station independently chooses one of two Boolean sides, so the full configuration type has cardinality two to the station count. This ambient count does not provide an orbit encoding.

**Theorem 1.2 (Mirroring complements the occupied support).**

$\forall s\in\operatorname{Stationing}(n),\ \operatorname{Occ}(M(s))=\operatorname{Fin}(n)\setminus\operatorname{Occ}(s)$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/StationingCombinatorics.occupied_stations_mirror` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Occupancy is the finite support of true Boolean coordinates. Pointwise negation sends that support to its complement inside the labeled station set; no sampled zero set is identified with this support.

**Theorem 1.3 (Mirror occupancy is the complementary count).**

$\forall s\in\operatorname{Stationing}(n),\ |\operatorname{Occ}(M(s))|=n-|\operatorname{Occ}(s)|$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/StationingCombinatorics.mirror_occupied_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking cardinalities in the support-complement identity gives the total station count minus the original occupancy. The finite identity supplies neither a density limit nor a repulsion exponent.

**Theorem 1.4 (Boolean mirroring has no fixed nonempty stationing).**

$\forall n>0,\ \forall s\in\operatorname{Stationing}(n),\ M(s)\neq s$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/StationingCombinatorics.mirror_stationing_ne_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty labeled station set, the value at index zero differs from its Boolean negation, so no stationing is fixed. Applying this action to arithmetic orbits still requires the unresolved orbit-to-stationing bridge.

**Theorem 1.5 (A prescribed occupancy has binomial cardinality).**

$\forall n,k\in\mathbb{N},\ \operatorname{card}\{s\in\operatorname{Stationing}(n):|\operatorname{Occ}(s)|=k\}=\operatorname{choose}(n,k)$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/StationingCombinatorics.occupied_count_stationing_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support equivalence identifies stationings with exactly k true coordinates and k-element subsets of the n labeled stations. Their exact count is the binomial coefficient; this does not prove either empirical zero-statistics law.

## References

- Truth anchor: `D5/S1/Depth/StationingCombinatorics.mirror_occupied_count`
- Truth anchor: `D5/S1/Depth/StationingCombinatorics.mirror_stationing_ne_self`
- Truth anchor: `D5/S1/Depth/StationingCombinatorics.occupied_count_stationing_count`
- Truth anchor: `D5/S1/Depth/StationingCombinatorics.occupied_stations_mirror`
- Truth anchor: `D5/S1/Depth/StationingCombinatorics.stationing_count`
