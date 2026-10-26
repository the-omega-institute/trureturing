# Closed-cap compatibility and weight transport

## Abstract

Closed-cap compatibility and weight transport.

**Theorem 1.1 (Closed-cap compatibility and weight transport).**

$$\forall L \in \mathit{Type},\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(m + 1\right), L\right),\; \forall b \in L,\; \operatorname{Partner}\left(M, \operatorname{CastSucc}\left(j\right)\right) = \operatorname{Succ}\left(j\right) \Rightarrow \left(\operatorname{Compatible}\left(M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \Leftrightarrow \operatorname{Compatible}\left(\operatorname{CapSurgery}\left(M, j\right), y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/ClosedCapFiber.close_compatible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When the original endpoints already form a pair, the inserted middle label is free. Compatibility of the full detour is equivalent to compatibility of the smaller matching for every middle label.

**Theorem 1.2 (Closed-cap compatibility and weight transport).**

$$\forall L \in \mathit{Type},\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall q \in \operatorname{Function}\left(L, \mathit{Real}\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(m + 1\right), L\right),\; \forall b \in L,\; \operatorname{Partner}\left(M, \operatorname{CastSucc}\left(j\right)\right) = \operatorname{Succ}\left(j\right) \Rightarrow \operatorname{BoundaryPotential}\left(q, M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \cdot \operatorname{Divide}\left(\operatorname{Apply}\left(q, b\right), \operatorname{Apply}\left(q, \operatorname{Apply}\left(y, j\right)\right)\right) = \operatorname{Square}\left(\operatorname{Divide}\left(\operatorname{Apply}\left(q, b\right), \operatorname{Apply}\left(q, \operatorname{Apply}\left(y, j\right)\right)\right)\right) \cdot \operatorname{BoundaryPotential}\left(q, \operatorname{CapSurgery}\left(M, j\right), y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/ClosedCapFiber.close_boundaryPotential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary real weights, multiplying the original boundary potential by the cap weight ratio gives its square times the smaller potential. The identity includes incompatible shorter labellings, where both sides vanish, and real division is the usual total field operation.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/ClosedCapFiber.close_boundaryPotential`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/ClosedCapFiber.close_compatible_iff`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/BoundaryProductTransport](BoundaryProductTransport.md)
