# Arbitrary symmetric-label cap surgery

## Abstract

Arbitrary symmetric-label cap surgery.

**Theorem 1.1 (Arbitrary symmetric-label cap surgery).**

$$\forall L \in \mathit{FiniteDecidableType},\; \forall R \in \operatorname{Relation}\left(L\right),\; \forall q \in \operatorname{Function}\left(L, \mathit{Real}\right),\; \forall s \in L,\; \forall m \in \mathit{Natural},\; \forall M \in \operatorname{NCMatching}\left(m + 2\right),\; \forall j \in \operatorname{Fin}\left(m + 1\right),\; \operatorname{Symmetric}\left(R\right) \Rightarrow \left(\left(\forall a \in L,\; \operatorname{Apply}\left(q, a\right) \ne 0\right) \Rightarrow \operatorname{CapFiberGoal}\left(R, q, s, m, M, j\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/Knot/CapSurgeryLabelFiber.capSurgery_labelFiber` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite label type, every symmetric relation, every everywhere nonzero real weight function, every root, every frontier size and every adjacent cap, the complete CapFiberGoal holds. The smaller noncrossing matching is constructed by the exact rewiring. In the closed case every neighbor lifts and the potential gains the squared cap ratio. In the nonclosed case compatibility is equivalent to existence of a unique legal neighbor, and each compatible lift has the exact potential identity. Self-loops, empty fibers, empty residual frontiers, negative nonzero weights and all nesting patterns remain in scope. This is an algebraic matching and legal-path statement; no circle evaluation, eigenvector hypothesis or topological invariant is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/Knot/CapSurgeryLabelFiber.capSurgery_labelFiber`
- Dependency: [D5/S3/Combinatorics/PerfectMatchings/NonclosedCapPotential](../../../Combinatorics/PerfectMatchings/NonclosedCapPotential.md)
- Dependency: [D5/S3/Quantum/Algebra/Knot/LegalCapFibers](LegalCapFibers.md)
