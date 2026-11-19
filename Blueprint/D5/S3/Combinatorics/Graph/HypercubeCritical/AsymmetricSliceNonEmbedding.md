# The explicit asymmetric slice does not embed inducedly in any finite cube

## Abstract

Refutation of the induced-cube embedding obligation for the explicit asymmetric 24-vertex, 32-edge slice.

This result excludes the explicit asymmetric 24-vertex slice candidate studied in the 48-vertex component analysis. Formal extraction of this graph from every slice with parameters (13,11;7,1) is not included. It does not exclude all 48-vertex candidates. Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2 (https://arxiv.org/html/2610.09483v1#Thmproblem2), and its original 258-point obligation remain unresolved; literature novelty is unconfirmed.

**Theorem 1.1 (Negation of the actual candidate embedding claim).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The literal closed definition claim is: there exist n : ℕ and f : Fin 24 → (Fin n → Bool) such that f is injective and, for all a,b : Fin 24, graph.Adj a b if and only if (hypercube n).Adj (f a) (f b). The theorem result has exactly type ¬ claim, without a certificate hypothesis or dimension restriction, including n = 0.

The label order is 0 X1, 1 X2, 2 Y1, 3 Y2, 4 a, 5 b, 6 c, 7 d, 8 e, 9 f, 10 low0, 11 low1, 12 low2, 13 low3, 14 low4, 15 low5, 16 low6, 17 u, 18 v, 19 x1, 20 x2, 21 y1, 22 y2, 23 z. The graph has exactly the following 32 undirected edges, with one orientation listed: (23,17),(23,18),(4,17),(4,19), (5,17),(5,20),(6,18),(6,21),(7,18),(7,22),(8,19), (8,21),(9,20),(9,22),(0,19),(1,20),(2,21),(3,22), (10,4),(10,3),(11,3),(11,2),(12,2),(12,5),(13,6), (13,1),(14,1),(14,0),(15,0),(15,7),(16,8),(16,9).

For each actual coordinate i set c(v) = f(v)(i). Reuse adjacent_exists_flip from BalancedCubeGirth and the generic flip from BalancedCriticalSpectrum. An adjacent pair crossing coordinate i must differ by exactly flip_i. On an actual two-edge path a-b-d with a ≠ d, crossing both edges would give f(a) = f(d), contradicting injectivity. On an actual three-edge path a-b-c-d with graph nonedge a-d, crossing its first and last edges gives f(a) = flip_i(f(b)) and f(d) = flip_i(f(c)). Simultaneous flipping preserves Hamming adjacency, so the middle edge implies a cube edge f(a)-f(d). Induced reflection contradicts the specified nonedge.

Forty-three static clauses each forbid simultaneous crossing of a selected pair of edges. The private paths_valid proof uses closed decide +kernel to check every selected edge and the required endpoint inequality or middle edge and endpoint nonedge. The local argument proves all these clauses for every actual coordinate cut. After reducing the static list to propositional clauses, grind supplies an ordinary kernel proof of their implication: the XOR of crossings of (17,23), (1,20), (12,2) is false. No completeness or minimality of the clause list, Python cut catalog, or external certificate hypothesis is assumed.

These three pairs are actual graph edges, checked by closed decide +kernel. Their images have flip coordinates i,j,k. At every coordinate t the certificate requires even parity of t=i, t=j, t=k. At t=i exactly one of j,k equals i. The other coordinate then occurs once, contradicting its own parity equation. Existence of the edge directions also handles the zero-dimensional case. All helper declarations are private and used by result.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/AsymmetricSliceNonEmbedding.result`
- Dependency: [D5/S3/Combinatorics/Graph/Hypercube](../Hypercube.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](BalancedCriticalSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCubeGirth](BalancedCubeGirth.md)
