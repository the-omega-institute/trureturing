# The p = 31 orientation instances have no solution

## Abstract

Garcia's four normalized AGL(1,31) orientation instances cannot avoid a cycle of length 64 after H15 vertex replacement.

**Definition 1.1 (Some orientation of Garcia's p = 31 instance avoids 64-cycles).**

Lean statement: `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each multiplier a in {11,17,22,24}, take the right Cayley graph of the affine group over ZMod(31), with generators t=(-1,0), g=(a,1), and r=inverse(g). An orientation sigma chooses one of these three incident edge types at each base vertex. A bijection tau at each vertex sends that chosen type to port u and sends the remaining types to v and w in either order. The literal replacement has a copy of the fifteen-vertex gadget at every base vertex, its listed internal edges, and one external edge joining the assigned attachment vertices for each Cayley edge. The claim asserts that some multiplier a, some orientation sigma, and some compatible family tau give a replacement with no simple cycle of length 64.

**Theorem 1.2 (The solvability assertion is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.result` (`✓ std3`). ∎

*Resolves.* `Problems/garcia-2026-erdos64-agl31-orientation` (refuted) by `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"garcia-2026-erdos64-agl31-orientation","declaration_gid":"D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Commentary.*

The p = 31 module supplies the four private certificate pairs tgtrrtrrrtgggg/tgtgtgtgtrtrrr, tgtggggtrrrtrr/tgtgtgtgtrrrtr, tgtgtrrrrrtggg/tgtgtrtggtrrtr, and tgtgtgggtrrrrr/tgtgtrtrrtggtr. The shared affine replacement theorem accepts their kernel-checked closure, prefix distinctness, incident-type partition and histograms.

Translated-visit averaging forces at least ten compatible visits in one certificate cycle. The explicit gadget paths and cyclic external edges expand those visits to a simple 64-cycle, contradicting the universal avoidance clause.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationThirtyOne.result`
- Dependency: [D5/S3/Combinatorics/Graph/ErdosGyarfasGarciaOrientationBase](ErdosGyarfasGarciaOrientationBase.md)
