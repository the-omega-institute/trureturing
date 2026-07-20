# Seat-Tower Combinatorics

## Abstract

Record exact parity and finite-cardinality skeletons for mirror stationing.

This module works with labeled finite indices, independent bounded exponent choices, and Boolean stationings. It does not identify arithmetic orbits with stationings, derive a selector from Jacobi data, or supply any finite orbit certificate. No finite observation, measured exponent, density, or asymptotic law is closed by these theorems.

**Theorem 1.1 (Reversal swaps parity in an even cycle).**

$\forall h,i\in\mathbb{N},\ i<2h \Rightarrow (2h-1-i)\operatorname{mod}2=1-(i\operatorname{mod}2)$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.reversal_swaps_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an index inside a cycle of length twice a half-length, the reversed index has the opposite parity. This is an index calculation, not the narrative identity between a reversed canonical word and a rotation.

**Theorem 1.2 (A parity-matching rotation has odd offset).**

$$\forall h,i,k\in\mathbb{N},\ i<2h \land (2h-1-i)\operatorname{mod}2=(i+k)\operatorname{mod}2 \Rightarrow k\operatorname{mod}2=1$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.matching_rotation_offset_is_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a rotated index is assumed to have the same parity as the reversed index, the rotation offset is odd. The premise connecting an actual periodic word to such a rotation remains explicit and unproved.

**Theorem 1.3 (Half of the offsets in an even cycle are even).**

$\forall h\in\mathbb{N},\ \operatorname{card}(\operatorname{EvenOffset}(h))=h$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.even_offset_skeleton_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Doubling gives an explicit equivalence from a half-length index type to the even offsets in the full cycle. The resulting count does not identify offsets with arithmetic orbit classes.

**Theorem 1.4 (Full exponent choices multiply).**

$$\forall p\in\mathbb{N},\ \forall e:\operatorname{Fin}(p)\to\mathbb{N},\ \operatorname{card}\!\left(\prod_{i\in\operatorname{Fin}(p)}\operatorname{Fin}(e(i)+1)\right)=\prod_{i\in\operatorname{Fin}(p)}(e(i)+1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.full_exponent_stationing_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For labeled factors with independent exponent bounds, the number of bounded allocations is the product of the local capacities. No orbit-to-allocation map or bijection is supplied.

**Theorem 1.5 (All labeled stationings have power-of-two cardinality).**

$\forall n\in\mathbb{N},\ \operatorname{card}(\operatorname{Stationing}(n))=2^n$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.stationing_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each labeled station independently chooses one of two Boolean sides, so the full configuration type has cardinality two to the station count. This ambient count does not assert that arithmetic orbits exhaust the Boolean model.

**Theorem 1.6 (Mirroring complements the occupied support).**

$\forall s\in\operatorname{Stationing}(n),\ \operatorname{Occ}(M(s))=\operatorname{Fin}(n)\setminus\operatorname{Occ}(s)$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.occupied_stations_mirror` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Occupancy is defined as the finite support of true Boolean coordinates. Pointwise negation therefore sends that support to its complement inside the labeled station set; no sampled zero set is identified with this support.

**Theorem 1.7 (Mirror occupancy is the complementary count).**

$\forall s\in\operatorname{Stationing}(n),\ |\operatorname{Occ}(M(s))|=n-|\operatorname{Occ}(s)|$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.mirror_occupied_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking cardinalities in the support-complement identity gives the total station count minus the original occupancy. The finite identity supplies neither a density limit nor a repulsion exponent.

**Theorem 1.8 (Boolean mirroring has no fixed nonempty stationing).**

$\forall n>0,\ \forall s\in\operatorname{Stationing}(n),\ M(s)\neq s$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.mirror_stationing_ne_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On a nonempty labeled station set, the value at index zero differs from its Boolean negation, so no stationing is fixed. Applying this fixed-point-free action to arithmetic orbits still requires the unresolved orbit-to-stationing bridge.

**Theorem 1.9 (A prescribed occupancy has binomial cardinality).**

$\forall n,k\in\mathbb{N},\ \operatorname{card}\{s\in\operatorname{Stationing}(n):|\operatorname{Occ}(s)|=k\}=\operatorname{choose}(n,k)$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.occupied_count_stationing_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The support equivalence identifies stationings with exactly k true coordinates and k-element subsets of the n labeled stations. Their exact count is the binomial coefficient; this does not prove either empirical zero-statistics law.

**Theorem 1.10 (Each Boolean mirror pair has a unique normalized member).**

$$\forall f\in\mathbb{N},\ \forall s\in\operatorname{Stationing}(f+1),\ \operatorname{Rep}(N(s)) \land (N(s)=s \lor N(s)=M(s)) \land \forall r,\ \operatorname{Rep}(r) \land (r=s \lor r=M(s)) \Rightarrow r=N(s)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.mirror_normalization_is_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise Boolean complement exchanges the two labeled sides. Choosing the member whose distinguished coordinate is false gives a unique representative among a stationing and its mirror.

**Theorem 1.11 (Mirror representatives have power-of-two cardinality).**

$$\forall f\in\mathbb{N},\ \operatorname{card}\{s\in\operatorname{Stationing}(f+1)\mid\operatorname{Rep}(s)\}=2^{f}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.mirror_representative_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After fixing the distinguished coordinate, all remaining Boolean coordinates are free, giving exactly two to the free-count representatives. This finite model implies no measured density or asymptotic exponent.
