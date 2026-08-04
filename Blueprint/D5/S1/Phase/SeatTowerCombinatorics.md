# Seat-Tower Combinatorics

## Abstract

Record exact parity and finite-cardinality skeletons for mirror stationing.

This module works with labeled finite indices, independent bounded exponent choices, and Boolean stationings. It does not identify arithmetic orbits with stationings, derive a selector from Jacobi data, or supply any finite orbit certificate. No finite observation, measured exponent, density, or asymptotic law is closed by these theorems.

<a id="describe-reversal-swaps-parity"></a>

**Theorem 1.1 (Reversal swaps parity in an even cycle).**

$\forall h,i\in\mathbb{N},\ i<2h \Rightarrow (2h-1-i)\operatorname{mod}2=1-(i\operatorname{mod}2)$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.reversal_swaps_parity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an index inside a cycle of length twice a half-length, the reversed index has the opposite parity. This is an index calculation, not the narrative identity between a reversed canonical word and a rotation.

<a id="describe-matching-rotation-offset-is-odd"></a>

**Theorem 1.2 (A parity-matching rotation has odd offset).**

$$\forall h,i,k\in\mathbb{N},\ i<2h \land (2h-1-i)\operatorname{mod}2=(i+k)\operatorname{mod}2 \Rightarrow k\operatorname{mod}2=1$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.matching_rotation_offset_is_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a rotated index is assumed to have the same parity as the reversed index, the rotation offset is odd. The premise connecting an actual periodic word to such a rotation remains explicit and unproved.

<a id="describe-even-offset-skeleton-count"></a>

**Theorem 1.3 (Half of the offsets in an even cycle are even).**

$\forall h\in\mathbb{N},\ \operatorname{card}(\operatorname{EvenOffset}(h))=h$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.even_offset_skeleton_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Doubling gives an explicit equivalence from a half-length index type to the even offsets in the full cycle. The resulting count does not identify offsets with arithmetic orbit classes.

<a id="describe-full-exponent-stationing-count"></a>

**Theorem 1.4 (Full exponent choices multiply).**

$$\forall p\in\mathbb{N},\ \forall e:\operatorname{Fin}(p)\to\mathbb{N},\ \operatorname{card}\!\left(\prod_{i\in\operatorname{Fin}(p)}\operatorname{Fin}(e(i)+1)\right)=\prod_{i\in\operatorname{Fin}(p)}(e(i)+1)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.full_exponent_stationing_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For labeled factors with independent exponent bounds, the number of bounded allocations is the product of the local capacities. No orbit-to-allocation map or bijection is supplied.

<a id="describe-mirror-normalization-is-unique"></a>

**Theorem 1.5 (Each Boolean mirror pair has a unique normalized member).**

$$\forall f\in\mathbb{N},\ \forall s\in\operatorname{Stationing}(f+1),\ \operatorname{Rep}(N(s)) \land (N(s)=s \lor N(s)=M(s)) \land \forall r,\ \operatorname{Rep}(r) \land (r=s \lor r=M(s)) \Rightarrow r=N(s)$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.mirror_normalization_is_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pointwise Boolean complement exchanges the two labeled sides. Choosing the member whose distinguished coordinate is false gives a unique representative among a stationing and its mirror.

<a id="describe-mirror-representative-count"></a>

**Theorem 1.6 (Mirror representatives have power-of-two cardinality).**

$$\forall f\in\mathbb{N},\ \operatorname{card}\{s\in\operatorname{Stationing}(f+1)\mid\operatorname{Rep}(s)\}=2^{f}$$

*Proof.* Machine-checked in Lean as `D5/S1/Phase/SeatTowerCombinatorics.mirror_representative_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After fixing the distinguished coordinate, all remaining Boolean coordinates are free, giving exactly two to the free-count representatives. This finite model implies no measured density or asymptotic exponent.

## References

- Truth anchor: `D5/S1/Phase/SeatTowerCombinatorics.even_offset_skeleton_count`
- Truth anchor: `D5/S1/Phase/SeatTowerCombinatorics.full_exponent_stationing_count`
- Truth anchor: `D5/S1/Phase/SeatTowerCombinatorics.matching_rotation_offset_is_odd`
- Truth anchor: `D5/S1/Phase/SeatTowerCombinatorics.mirror_normalization_is_unique`
- Truth anchor: `D5/S1/Phase/SeatTowerCombinatorics.mirror_representative_count`
- Truth anchor: `D5/S1/Phase/SeatTowerCombinatorics.reversal_swaps_parity`
