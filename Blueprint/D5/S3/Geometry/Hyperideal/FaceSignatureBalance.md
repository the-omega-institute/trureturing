# Face signatures and opposite-pair balance

## Abstract

Equal face signatures characterize opposite-pair balance in a tetrahedral edge coloring.

Number the local edges (12,13,14,34,24,23). A Boolean coloring marks each local edge as low (true) or high (false). The four faces omit vertices 1, 2, 3, 4 respectively, and faceLowCount counts the three low edge occurrences on each face.

**Theorem 1.1 (Equal signatures force opposite edges to agree).**

$$\forall low \in Fin\left(6\right) \to Bool,\; \left(\forall i \in Fin\left(4\right), j \in Fin\left(4\right),\; faceLowCount\left(low, i\right) = faceLowCount\left(low, j\right)\right) \Leftrightarrow \left(low\left(0\right) = low\left(3\right) \land \left(low\left(1\right) = low\left(4\right) \land low\left(2\right) = low\left(5\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FaceSignatureBalance.equal_face_counts_iff_opposite_balance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every coloring of all six local edges, the four face counts are pairwise equal exactly when edges 12 and 34, 13 and 24, and 14 and 23 have matching colors. No restriction is placed on the number of low edges.

The three differences among the four face counts recover the three opposite-pair color differences. Conversely, each face contains exactly one member of each opposite pair. The finite six-color computation establishes both directions.

This is a local incidence statement. It does not assert that faces have been paired into a manifold or that any geometric edge lengths or angles exist.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FaceSignatureBalance.equal_face_counts_iff_opposite_balance`
