# Complete source objects and retained trust boundaries

## Abstract

The exact six-dimensional source representation and certificate.

**Definition 1.1 (exact low bits).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.bits`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.bits` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Coordinate i is precisely the ith low bit of the integer mask. All six coordinates are retained.

**Definition 1.2 (actual vector space equivalence).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.vectorLinearEquiv`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.vectorLinearEquiv` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The mask wrapper carries the binary vector-space operations transported by the actual low-bit bijection. Its addition agrees with source XOR, as checked separately; it is not arithmetic modulo 64.

**Definition 1.3 (complete space lattice equivalence).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.spaceEquiv`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.spaceEquiv` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

Every zero-containing XOR-closed finite mask set corresponds to exactly its image Submodule, and every actual coordinate submodule is obtained. Scalar closure is proved for both binary scalars.

**Definition 1.4 (nonzero space equivalence).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.vertexEquiv`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.vertexEquiv` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The source zero space {0} corresponds exactly to bottom. Thus all nonzero spaces, including top, correspond in both directions.

**Definition 1.5 (full orthogonality graph isomorphism).**

Lean statement: `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.graphIso`

*Formalization.* `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.graphIso` (`✓ std3`).

*Citation.* Haobo Ma; Reza Nikandish; Wenlin Zhang (2026). *Clique and chromatic numbers of binary subspace orthogonality graphs: original versions and formal certificate*. URL: <https://github.com/the-omega-institute/binary-subspace-orthogonality>.

*Commentary.*

The exact low-bit dot-zero equivalence proves the source and actual Submodule graphs are isomorphic, preserving distinctness and every cross pairing. Transferring the supplied chromatic theorem remains a transient exact application, not a duplicated public theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.bits`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.graphIso`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.spaceEquiv`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.vectorLinearEquiv`
- Truth anchor: `D5/S3/Combinatorics/Orthogonality/SixBitSubmoduleBridge.vertexEquiv`
- Dependency: [D5/S3/Combinatorics/Orthogonality/NikandishClique](NikandishClique.md)
- Dependency: [D5/S3/Combinatorics/Orthogonality/SixBitCatalogue](SixBitCatalogue.md)
