# Cigler's Signed Strip and Cycle Walk Identities

## Abstract

Signed Dyck paths in the strip of height 4k minus two count walks on the cycle with 4k vertices.

**Theorem 1.1 (The three cycle walk equalities).**

Lean statement: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalk.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalk.result` (`✓ std3`). ∎

*Resolves.* `Problems/cigler-signed-strip-cycle-walks` (proved) by `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalk.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cigler-signed-strip-cycle-walks","declaration_gid":"D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalk.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Johann Cigler (2026). *Some sequences and number triangles which are related to Narayana polynomials and to q-Narayana polynomials for q=-1*. DOI: [10.48550/arXiv.2608.03363](https://doi.org/10.48550/arXiv.2608.03363). URL: <https://arxiv.org/abs/2608.03363v2>.

*Commentary.*

For every integer k at least one and every nonnegative integer n, let c_r be the sum of the weights of Dyck paths of semilength r confined to heights zero through 4k minus two. Up-steps have weight one, and down-steps arriving at height j have weight (-1)^floor(j/2), repeating 1, 1, minus one, minus one. If U_k is the adjacency matrix of the cycle on 4k vertices, then c_{2n+1} = U_k^{2n+1}(0, 1) and c_{2n+2} = U_k^{2n+2}(0, 0) = 2c_{2n+1}. These are Conjecture 1, equation (74), of Cigler's paper. Pairing steps and factoring their transfer matrix identifies c_r for positive r with closed walks at an endpoint of the 2k-vertex path with a loop at each end. Folding the 4k-cycle expresses this count as the sum of walks from zero to zero and from zero to minus one. Parity eliminates one endpoint at each length, and reflection together with the one-step recurrence gives the factor two.

## References

- Truth anchor: `D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalk.result`
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerCycleWalkFolding](CiglerCycleWalkFolding.md)
