# Signed Strip Sums and Cycle Walks

## Abstract

Signed Dyck path sums in bounded strips are compared with counts of walks on finite cycles.

**Definition 1.1 (Walks with a prescribed endpoint).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs.walkCount`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs.walkCount` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For natural numbers N and r and a residue a modulo N, walkCount counts the Boolean sequences of length r whose increments sum to a modulo N. A true entry contributes one and a false entry contributes minus one. For N at least three, this is the number of walks of length r from zero to a on the N-cycle. The two step choices are counted separately even when they give the same residue. For N equal to zero the endpoint is an integer rather than a residue in a finite cycle.

**Definition 1.2 (Signed Dyck paths in a strip).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs.signedStrip`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs.signedStrip` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For natural numbers H and r, signedStrip is the integer sum of the weights of Dyck paths of semilength r confined to heights zero through H, inclusive. Every up-step has weight one, and a down-step arriving at height j has weight (-1)^floor(j/2). Thus the down-step weights repeat 1, 1, minus one, minus one. This sum is the signed Narayana strip polynomial evaluated at t = 1.

**Definition 1.3 (The strip and cycle identities).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs.claim`

*Formalization.* `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every integer k at least one and every nonnegative integer n, write c_r for the signed Dyck path sum of semilength r in the strip of height 4k minus two, and U_k for the adjacency matrix of the cycle on 4k vertices. The assertion is c_{2n+1} = U_k^{2n+1}(0, 1), c_{2n+2} = U_k^{2n+2}(0, 0), and U_k^{2n+2}(0, 0) = 2c_{2n+1}. Each matrix entry counts walks of the indicated length and endpoints. These are the three equalities in Conjecture 1, equation (74), of Cigler's paper.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs.claim`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs.signedStrip`
- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkDefs.walkCount`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs](CiglerStripExpansionDefs.md)
