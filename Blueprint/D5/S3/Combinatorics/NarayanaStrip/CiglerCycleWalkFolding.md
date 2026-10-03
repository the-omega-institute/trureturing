# Folding an Even Cycle

## Abstract

Reflection folds an even cycle onto a path with endpoint loops and relates their walk counts.

**Definition 1.1 (The cycle transition matrix).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.cycleAdj`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.cycleAdj` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For a positive integer N, cycleAdj is the integer matrix on residues modulo N. Its entry from s to t is the sum of the indicator that s plus one equals t and the indicator that s minus one equals t, with all equalities taken modulo N. For N at least three this is the adjacency matrix of the N-cycle. For N equal to one or two, coincident step destinations are counted with multiplicity two.

**Definition 1.2 (Reflection onto a half-cycle).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.fold`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.fold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For a positive integer v and a residue on the cycle of length 2v, let j be its representative between zero and 2v minus one. Its folded vertex is min(j, 2v - 1 - j), which lies between zero and v minus one. Thus the reflection exchanging j and 2v minus one minus j identifies each reflected pair of vertices.

**Theorem 1.3 (Closed folded walks and two cycle endpoints).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.folded_moment_eq_walkCount`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.folded_moment_eq_walkCount` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every integer v at least two and every nonnegative integer r, foldedAdj(v)^r(0, 0) equals the number of r-step walks on the 2v-cycle from zero to zero plus the number from zero to minus one. Folding intertwines the cycle adjacency matrix with the adjacency matrix of the v-vertex path with a loop at each end. The two cycle vertices lying over the first path vertex are zero and minus one.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.cycleAdj`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.fold`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding.folded_moment_eq_walkCount`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkTransfer](CiglerCycleWalkTransfer.md)
