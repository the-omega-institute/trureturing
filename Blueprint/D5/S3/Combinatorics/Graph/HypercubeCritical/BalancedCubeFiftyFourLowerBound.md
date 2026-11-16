# A lower bound of 54 for nonempty balanced cubic cube restrictions

## Abstract

Nonempty balanced cubic induced subgraphs of Q9 have at least 54 vertices.

Hong, Wu and Xia, Graph Sensitivity of Cartesian Products with Matched Bridges, arXiv:2610.09483v1, section 7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), ask whether f₂(Q₉) is three or four. The original problem remains unresolved. This repository-derived lower bound concerns nonempty actual induced cubic subgraphs satisfying BalancedCriticalSpectrum.IsBalanced. It does not exclude all 258-vertex candidates, supply a witness, establish attainment of 54 or uniqueness, or assert literature priority.

Balance uses the original FALSE-prefix Huang signing: on selected actual cube edges the signed matrix entry is sigma(x) sigma(y), with sigma equal to plus or minus one on the selected set. The coordinate-zero slice remains a subset of Q9 with the same adjacency and signing. Connectedness is not assumed, and no replacement abstract graph, supplied cycle or label certificate is a hypothesis.

**Definition 1.1 (claim).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound.claim`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The closed proposition asserts the existence of C : Finset (Q 9) such that C is nonempty, its actual induced hypercube graph is regular of degree three, BalancedCriticalSpectrum.IsBalanced C holds for the original Huang signing, and C.card < 54. All graph and balance conditions concern this same C.

**Theorem 1.2 (result).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The result has literally type Not claim. Thus every nonempty balanced actual induced cubic subgraph of Q9 has cardinality at least 54. Lean kernel checking supplies the evidence; no trusted SAT output, native_decide or new axiom is used.

BalancedCubeLowerBound.forty_eight_le_card and the directional identity 6 * directionEdges C 0 = C.card force C.card = 48 and q = directionEdges C 0 = 8 under the contrary assumption. Reuse the actual smaller coordinate-zero slice S. Its size N is at most 24, exactly eight vertices have degree two, all others have degree three, the degree-two vertices are independent, and restricted balance gives girth at least eight.

Actual cube parity gives sides L,R. Put a=|L|, b=|R|, p=|degreeTwo G L|, r=|degreeTwo G R|, h=|degreeThree G L| and k=|degreeThree G R|. Then p+r=8, a=p+h, b=r+k, a+b=N, 2p+3h=2r+3k and 40 ≤ 3N. GirthSliceCounting supplies 15h ≤ h*b+2k+4r and 15k ≤ k*a+2h+4p. The degree balance forces p to be 1,4 or 7. Finite integer case analysis on the remaining side size proves that the only ordered tuples (a,b;p,r) are (11,11;4,4), (13,11;7,1), (11,13;1,7) and (12,12;4,4). This computation proves necessary conditions for the actual slice; it does not assume an explicit labelled obstruction.

SymmetricSliceExclusion excludes the first tuple, and AsymmetricSliceExclusion excludes the next two, swapping the actual bipartition for (11,13;1,7). SymmetricTwentyFourExclusion excludes the final tuple using the actual degree, girth and induced-cube conditions. Finite graph relabelling preserves all these conditions and the side and degree-two counts. The full inference uses the geometry and breadth-first counting of that exclusion, rather than postulating a cycle or classifying the actual slice as a guessed labelled graph.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeFiftyFourLowerBound.result`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceExclusion](AsymmetricSliceExclusion.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeLowerBound](BalancedCubeLowerBound.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSliceExclusion](SymmetricSliceExclusion.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricTwentyFourExclusion](SymmetricTwentyFourExclusion.md)
