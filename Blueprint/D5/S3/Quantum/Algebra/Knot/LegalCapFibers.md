# Adjacent cap fibers of rooted legal paths

## Abstract

Adjacent cap fibers of rooted legal paths.

**Definition 1.1 (Adjacent cap fibers of rooted legal paths).**

$$\forall L \in \mathit{FiniteDecidableType},\; \forall R \in \operatorname{Relation}\left(L\right),\; \forall s \in L,\; \forall m \in \mathit{Natural},\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall y \in \operatorname{LegalPath}\left(R, m, s, s\right),\; \forall b \in \operatorname{NeighborLabels}\left(R, \operatorname{Apply}\left(y, j\right)\right),\; \operatorname{Symmetric}\left(R\right) \Rightarrow \operatorname{UnderlyingLabels}\left(\operatorname{LegalDetour}\left(R, s, j, y, b\right)\right) = \operatorname{DetourLabels}\left(j, y, b\right)$$

*Formalization.* `D5/S3/Quantum/Algebra/Knot/LegalCapFibers.legalDetour` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A neighbor of the cap gap gives a genuine rooted legal detour of length two more. Symmetry of the relation supplies its reverse edge, the original endpoints stay fixed, and every unaffected edge comes from the original path.

**Theorem 1.2 (Adjacent cap fibers of rooted legal paths).**

$$\forall L \in \mathit{FiniteDecidableType},\; \forall R \in \operatorname{Relation}\left(L\right),\; \forall q \in \operatorname{Function}\left(L, \mathit{Real}\right),\; \forall s \in L,\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall y \in \operatorname{LegalPath}\left(R, m, s, s\right),\; \operatorname{Partner}\left(M, \operatorname{CastSucc}\left(j\right)\right) = \operatorname{Succ}\left(j\right) \Rightarrow \left(\left(\forall b \in \operatorname{NeighborLabels}\left(R, \operatorname{Apply}\left(y, j\right)\right),\; \operatorname{Compatible}\left(M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \Leftrightarrow \operatorname{Compatible}\left(\operatorname{CapSurgery}\left(M, j\right), y\right)\right) \land \left(\forall b \in \operatorname{NeighborLabels}\left(R, \operatorname{Apply}\left(y, j\right)\right),\; \operatorname{BoundaryPotential}\left(q, M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \cdot \operatorname{Divide}\left(\operatorname{Apply}\left(q, b\right), \operatorname{Apply}\left(q, \operatorname{Apply}\left(y, j\right)\right)\right) = \operatorname{Square}\left(\operatorname{Divide}\left(\operatorname{Apply}\left(q, b\right), \operatorname{Apply}\left(q, \operatorname{Apply}\left(y, j\right)\right)\right)\right) \cdot \operatorname{BoundaryPotential}\left(q, \operatorname{CapSurgery}\left(M, j\right), y\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/LegalCapFibers.capSurgery_close_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closed compatibility and squared-weight identities hold for the complete neighbor fiber, including empty fibers.

**Theorem 1.3 (Adjacent cap fibers of rooted legal paths).**

$$\forall L \in \mathit{FiniteDecidableType},\; \forall R \in \operatorname{Relation}\left(L\right),\; \forall s \in L,\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \forall y \in \operatorname{LegalPath}\left(R, m, s, s\right),\; \operatorname{Partner}\left(M, \operatorname{CastSucc}\left(j\right)\right) \ne \operatorname{Succ}\left(j\right) \Rightarrow \left(\operatorname{Symmetric}\left(R\right) \Rightarrow \left(\operatorname{Compatible}\left(\operatorname{CapSurgery}\left(M, j\right), y\right) \Leftrightarrow \left(\exists b \in \operatorname{NeighborLabels}\left(R, \operatorname{Apply}\left(y, j\right)\right),\; \operatorname{Compatible}\left(M, \operatorname{DetourLabels}\left(j, y, b\right)\right) \land \left(\forall c \in \operatorname{NeighborLabels}\left(R, \operatorname{Apply}\left(y, j\right)\right),\; \operatorname{Compatible}\left(M, \operatorname{DetourLabels}\left(j, y, c\right)\right) \Rightarrow c = b\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/LegalCapFibers.nonclose_legal_fiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonclosed compatible middle label is a genuine neighbor. Its legality follows from the surviving path edge and symmetry, and subtype extensionality gives uniqueness. No nonempty path-space assumption is required.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Knot/LegalCapFibers.capSurgery_close_fiber`
- Truth anchor: `D5/S3/Quantum/Algebra/Knot/LegalCapFibers.legalDetour`
- Truth anchor: `D5/S3/Quantum/Algebra/Knot/LegalCapFibers.nonclose_legal_fiber`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/NonclosedCapLabels](../../../Combinatorics/PerfectMatchings/NonclosedCapLabels.md)
- Dependency: [D5/S3/Quantum/Algebra/Knot/CapFiberContract](CapFiberContract.md)
