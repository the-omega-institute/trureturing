# Degree-Two Simplex Cochain Repair

## Abstract

Tetrahedral defects count anchored triangle repairs and detect exact edge cochains.

**Definition 1.1 (Anchored triangle errors).**

Lean statement: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.faceErrors`

*Formalization.* `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.faceErrors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an ordered triangle cochain F and vertex r, E(r) counts triples (i,j,k) for which F(i,j,k) differs from F(r,j,k)-F(r,i,k)+F(r,i,j). Repeated vertices are included.

**Definition 1.2 (Tetrahedral defects).**

Lean statement: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.tetraDefects`

*Formalization.* `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.tetraDefects` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T counts ordered quadruples (r,i,j,k) for which F(i,j,k)-F(r,j,k)+F(r,i,k)-F(r,i,j) is nonzero. Repeated vertices are included.

**Definition 1.3 (Edge-cochain triangle errors).**

Lean statement: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.edgeErrors`

*Formalization.* `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.edgeErrors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any edge cochain a, Err(a) counts ordered triples (i,j,k) for which F(i,j,k) differs from a(j,k)-a(i,k)+a(i,j). Repeated vertices are included.

**Theorem 1.4 (Incidence, repair, and exactness).**

$$\sum_{r \in V} E(r) = T\quad\land\quad(\exists r \in V, nE(r) \leq T)\quad\land\quad(\forall a, T \leq 4nErr(a))\quad\land\quad((dF = 0) \iff (\exists a, F = da))$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a nonempty finite vertex type, A an additive commutative group, and F any ordered triangle cochain with values in A. Write n for the number of vertices. The sum of anchored errors E(r) equals the total tetrahedral defect count T, and some anchor has n E(r) at most T. For every edge cochain a, T is at most 4n Err(a).

A defective tetrahedron has an erroneous face for every a. Each ordered face occurs in n tetrahedra in each of four positions. The tetrahedral defect vanishes at every ordered quadruple exactly when an edge cochain a satisfies F(i,j,k)=a(j,k)-a(i,k)+a(i,j) at every ordered triple. In that direction a(i,j)=F(r,i,j) for any fixed anchor r. No alternating condition on F or torsion condition on A is needed.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.edgeErrors`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.faceErrors`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.tetraDefects`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/SimplexTwoCochainRepair.tetra_defects_incidence_repair_and_exactness`
