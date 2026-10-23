# The unique middle label of a reconnected cap

## Abstract

The unique middle label of a reconnected cap.

**Theorem 1.1 (The unique middle label of a reconnected cap).**

$$\forall L \in \mathit{Type},\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(m + 1\right), L\right),\; \operatorname{Partner}\left(M, \operatorname{CastSucc}\left(j\right)\right) \ne \operatorname{Succ}\left(j\right) \Rightarrow \left(\operatorname{Compatible}\left(\operatorname{CapSurgery}\left(M, j\right), y\right) \Rightarrow \operatorname{Apply}\left(y, j\right) = \operatorname{Apply}\left(y, \operatorname{Succ}\left(\operatorname{CapU}\left(M, j\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/NonclosedCapLabels.cap_outer_label` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partner-closed intervals transport the labels through all intervening arcs in every relative-order case of a nonclosed cap.

**Theorem 1.2 (The unique middle label of a reconnected cap).**

$$\forall L \in \mathit{Type},\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(m + 1\right), L\right),\; \forall b \in L,\; \operatorname{Partner}\left(M, \operatorname{CastSucc}\left(j\right)\right) \ne \operatorname{Succ}\left(j\right) \Rightarrow \left(\operatorname{Compatible}\left(M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \Leftrightarrow \left(\operatorname{Compatible}\left(\operatorname{CapSurgery}\left(M, j\right), y\right) \land b = \operatorname{Apply}\left(y, \operatorname{CastSucc}\left(\operatorname{CapU}\left(M, j\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/NonclosedCapLabels.nonclose_compatible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Compatibility after reconnecting the two original partners is equivalent to compatibility before surgery with exactly the prescribed middle label. Both side equations and every surviving endpoint are retained.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/NonclosedCapLabels.cap_outer_label`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/NonclosedCapLabels.nonclose_compatible_iff`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/ClosedCapFiber](ClosedCapFiber.md)
