# Triangle Defects and Potential Errors

## Abstract

Triangle defects count anchored disagreements and are bounded by every potential's edge errors.

**Definition 1.1 (Anchored edge disagreements).**

Lean statement: `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.edgeDefects`

*Formalization.* `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.edgeDefects` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an edge label a and anchor r, E(r) counts all ordered pairs (i,j) for which a(i,j) differs from a(r,j)-a(r,i). Repeated vertices are included.

**Definition 1.2 (Oriented triangle defects).**

Lean statement: `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.triangleDefects`

*Formalization.* `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.triangleDefects` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T counts all ordered triples (r,i,j) for which a(r,i)+a(i,j)+a(j,r) is nonzero, including repeated vertices.

**Definition 1.3 (Potential edge errors).**

Lean statement: `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.potentialErrors`

*Formalization.* `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.potentialErrors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Err(p) counts ordered pairs (i,j) with a(i,j) different from p(j)-p(i). Diagonal pairs are included in the count.

**Theorem 1.4 (Incidence and universal potential error bound).**

$$\sum_{r \in V} E(r) = T\quad\land\quad\exists r \in V, nE(r) \leq T\quad\land\quad\forall p, T \leq 3(n-2)Err(p)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let V be a nonempty finite vertex type, A any additive commutative group, and a an edge labeling with a(i,i)=0 and a(j,i)=-a(i,j) for all vertices. Write n for the number of vertices. The exact ordered incidence identity sum_r E(r)=T holds, an anchor r has n E(r)<=T, and every potential p satisfies T<=3(n-2)Err(p), with natural-number subtraction. No division is used.

A defective triangle has an erroneous edge for every p. Repeated-vertex triangles vanish by alternation. For distinct triples, each erroneous ordered edge occurs in three cyclic positions and has n-2 choices for the third vertex. The proof also selects a minimum E(r). The result includes n=1,2 and groups with 2-torsion.

## References

- Truth anchor: `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.edgeDefects`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.potentialErrors`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.triangleDefects`
- Truth anchor: `D5/S3/Fourier/CharacterSelection/TriangleDefectStability.triangle_defects_incidence_repair_and_error_bound`
