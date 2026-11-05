# Mixed graph matrices and spectral signature

## Abstract

The spectral signature of a graph Laplacian plus a positive adjacency weight is nonincreasing.

**Definition 1.1 (Disjoint spanning edge partition).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall F \in \operatorname{SimpleGraph}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{IsEdgePartition}\left(F, G, H\right) = (\operatorname{Disjoint}\left(G, H\right) \land G \cup H = F)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BonettoSignature.IsEdgePartition` (`✓ std3`).

*Citation.* Riccardo Bonetto; Hildeberto Jardón Kojakhmetov (2024). *On the Eigenvalues of Graphs with Mixed Algebraic Structure*. URL: <https://arxiv.org/html/2408.00487v1>.

*Commentary.*

F, G and H are simple undirected loopless graphs on the same finite vertex type V. Disjoint G H means their edge sets are disjoint; G ∪ H = F means their union is exactly the original graph. The common vertex type makes the two subgraphs spanning. This is Definition 3, with no connectivity or nonempty-edge requirement.

**Definition 1.2 (The actual real graph matrix).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(V\right),\; \forall u \in \operatorname{Real},\; \operatorname{mixedMatrix}\left(G, H, u\right) = \operatorname{SimpleGraph}.\operatorname{lapMatrix}\left(G, \operatorname{Real}\right) + u \cdot \operatorname{SimpleGraph}.\operatorname{adjMatrix}\left(H, \operatorname{Real}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BonettoSignature.mixedMatrix` (`✓ std3`).

*Citation.* Riccardo Bonetto; Hildeberto Jardón Kojakhmetov (2024). *On the Eigenvalues of Graphs with Mixed Algebraic Structure*. URL: <https://arxiv.org/html/2408.00487v1>.

*Commentary.*

Definitions 1–3 give the ordinary symmetric 0/1 adjacency matrix A_H and combinatorial Laplacian L_G = D_G − A_G, whose diagonal entries are the vertex degrees. mixedMatrix G H u is exactly L_G + u A_H over the reals. The expression is defined for every real u; the conclusion uses only strictly positive parameters. Mathlib's SimpleGraph matrices provide this realization directly.

**Definition 1.3 (Signature with algebraic multiplicity).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall Q \in \operatorname{Matrix}\left(V, V, \operatorname{Real}\right),\; \operatorname{signature}\left(Q\right) = (\operatorname{card}\left(\operatorname{filter}\left((\lambda x \mapsto 0 < x), \operatorname{Polynomial}.\operatorname{roots}\left(\operatorname{Matrix}.\operatorname{charpoly}\left(Q\right)\right)\right)\right): \operatorname{Int}) - (\operatorname{card}\left(\operatorname{filter}\left((\lambda x \mapsto x < 0), \operatorname{Polynomial}.\operatorname{roots}\left(\operatorname{Matrix}.\operatorname{charpoly}\left(Q\right)\right)\right)\right): \operatorname{Int})$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/BonettoSignature.signature` (`✓ std3`).

*Citation.* Riccardo Bonetto; Hildeberto Jardón Kojakhmetov (2024). *On the Eigenvalues of Graphs with Mixed Algebraic Structure*. URL: <https://arxiv.org/html/2408.00487v1>.

*Commentary.*

Definitions 7 and 8 count positive and negative eigenvalues with multiplicity and subtract the latter count from the former in the integers. Here roots is the multiset of real roots of the actual characteristic polynomial, filter preserves multiplicity, and card is its multiset cardinality. Zero roots pass neither strict sign filter. For each Hermitian real Q, Matrix.IsHermitian.roots_charpoly_eq_eigenvalues identifies this entire multiset with the indexed spectral eigenvalues. Thus the definition equals RHLinalg.posIndex minus RHLinalg.negIndex; no spectral realization is assumed. Only real symmetric matrices are used in the conclusion.

**Theorem 1.4 (Signature monotonicity on the positive axis).**

$$\forall V \in \operatorname{Type},\; [\operatorname{Fintype}\left(V\right)] [\operatorname{DecidableEq}\left(V\right)] \forall F \in \operatorname{SimpleGraph}\left(V\right),\; \forall G \in \operatorname{SimpleGraph}\left(V\right),\; \forall H \in \operatorname{SimpleGraph}\left(V\right),\; \operatorname{IsEdgePartition}\left(F, G, H\right) \Rightarrow \left(\forall s \in \operatorname{Real},\; \forall t \in \operatorname{Real},\; \left(0 < s \land s \le t\right) \Rightarrow \operatorname{signature}\left(\operatorname{mixedMatrix}\left(G, H, t\right)\right) \le \operatorname{signature}\left(\operatorname{mixedMatrix}\left(G, H, s\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/BonettoSignature.result` (`✓ std3`). ∎

*Resolves.* `Problems/bonetto-jardon-kojakhmetov-2024-signature-monotonicity` (proved) by `D5/S3/Combinatorics/SpectralGraph/BonettoSignature.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"bonetto-jardon-kojakhmetov-2024-signature-monotonicity","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/BonettoSignature.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Riccardo Bonetto; Hildeberto Jardón Kojakhmetov (2024). *On the Eigenvalues of Graphs with Mixed Algebraic Structure*. URL: <https://arxiv.org/html/2408.00487v1>.

*Commentary.*

This is the nonincreasing assertion of Section 3, Conjecture 1. Every finite vertex type, including the empty type, every disjoint spanning edge partition and all 0 < s ≤ t are quantified. Singular matrices, persistent kernels, disconnected graphs, empty edge classes and s = t remain included. The partition fixes the original graph interpretation; the argument itself needs only L_G ≥ 0 and symmetry. Write M(u) = L_G + u A_H. The identities M(s) = (s/t)M(t) + (1−s/t)L_G and −M(t) = (t/s)(−M(s)) + (t/s−1)L_G have strictly positive first coefficients and nonnegative second coefficients. Consequently every subspace positive for M(t) is positive for M(s), and every subspace positive for −M(s) is positive for −M(t). RHLinalg.posIndex_eq_max_finrank_posDefOn and finrank_le_posIndex_of_posDefOn turn these transfers into Nplus(M(t)) ≤ Nplus(M(s)) and Nminus(M(s)) ≤ Nminus(M(t)); the existing posIndex_neg_eq_negIndex supplies the sign reversal. Subtracting the integer counts proves the displayed inequality. This assembly uses established spectral and inertia ingredients. No eigenvalue continuity, inverse matrix, generic crossing or kernel removal is required. It asserts no transition-count bound or limiting-signature formula. Bounded literature checks do not establish global novelty or priority.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BonettoSignature.IsEdgePartition`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BonettoSignature.mixedMatrix`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BonettoSignature.result`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/BonettoSignature.signature`
- Dependency: [D5/S3/SpectralTopology/FiniteSpectralLocalizer](../../SpectralTopology/FiniteSpectralLocalizer.md)
