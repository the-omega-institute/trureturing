# Insertion of an adjacent labelled detour

## Abstract

Insertion of an adjacent labelled detour.

**Theorem 1.1 (Insertion of an adjacent labelled detour).**

$$\forall L \in \mathit{Type},\; \forall m \in \mathit{Natural},\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(m + 1\right), L\right),\; \forall b \in L,\; \forall k \in \operatorname{Fin}\left(m\right),\; \operatorname{Apply}\left(\operatorname{DetourLabels}\left(j, y, b\right), \operatorname{CastSucc}\left(\operatorname{SkipPair}\left(j, k\right)\right)\right) = \operatorname{Apply}\left(y, \operatorname{CastSucc}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DetourLabels.detour_skip_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inserting the two cap endpoints leaves the left gap label of every surviving endpoint unchanged under the increasing survivor map.

**Theorem 1.2 (Insertion of an adjacent labelled detour).**

$$\forall L \in \mathit{Type},\; \forall m \in \mathit{Natural},\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(m + 1\right), L\right),\; \forall b \in L,\; \forall k \in \operatorname{Fin}\left(m\right),\; \operatorname{Apply}\left(\operatorname{DetourLabels}\left(j, y, b\right), \operatorname{Succ}\left(\operatorname{SkipPair}\left(j, k\right)\right)\right) = \operatorname{Apply}\left(y, \operatorname{Succ}\left(k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/DetourLabels.detour_skip_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same transport holds for right gap labels. At the cap the three successive labels are the original gap label, the inserted middle label, and the original gap label again.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DetourLabels.detour_skip_left`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/DetourLabels.detour_skip_right`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/AdjacentCapSurgery](AdjacentCapSurgery.md)
