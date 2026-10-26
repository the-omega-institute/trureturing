# Exact nonclosed-cap boundary potential

## Abstract

Exact nonclosed-cap boundary potential.

**Theorem 1.1 (Exact nonclosed-cap boundary potential).**

$$\forall L \in \mathit{Type},\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall q \in \operatorname{Function}\left(L, \mathit{Real}\right),\; \forall y \in \operatorname{Function}\left(\operatorname{Fin}\left(m + 1\right), L\right),\; \forall b \in L,\; \operatorname{Partner}\left(M, \operatorname{CastSucc}\left(j\right)\right) \ne \operatorname{Succ}\left(j\right) \Rightarrow \left(\left(\forall a \in L,\; \operatorname{Apply}\left(q, a\right) \ne 0\right) \Rightarrow \left(\operatorname{Compatible}\left(M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \Rightarrow \operatorname{BoundaryPotential}\left(q, M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \cdot \operatorname{Divide}\left(\operatorname{Apply}\left(q, b\right), \operatorname{Apply}\left(q, \operatorname{Apply}\left(y, j\right)\right)\right) = \operatorname{BoundaryPotential}\left(q, \operatorname{CapSurgery}\left(M, j\right), y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/NonclosedCapPotential.nonclose_boundaryPotential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary finite label type and everywhere nonzero real weights, a compatible detour satisfies the nonclosed-cap potential identity. The affected opening factors cancel using nonvanishing, while the entire unaffected product remains common. No positivity, eigenvector equation, or special label graph is assumed.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/NonclosedCapPotential.nonclose_boundaryPotential`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/NonclosedCapLabels](NonclosedCapLabels.md)
