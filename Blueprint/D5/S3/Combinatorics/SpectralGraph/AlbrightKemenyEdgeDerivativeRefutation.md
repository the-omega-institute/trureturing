# The path-ends derivative does not minimize Kemeny's edge derivative

## Abstract

A connected barbell on 23 vertices has a smaller Kemeny edge derivative than the path.

The edge weight varies by a real parameter t, and weighted degrees vary with it. Kemeny's constant is the sum of reciprocals of the nonzero eigenvalues of the normalized Laplacian, counted with multiplicity.

**Definition 1.1 (One-edge perturbation).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall a \in \operatorname{Fin}\left(n\right),\; \forall b \in \operatorname{Fin}\left(n\right),\; \forall t \in \mathrm{Real},\; \operatorname{paramAdj}\left(G, a, b, t\right) = \operatorname{SimpleGraph}.\operatorname{adjMatrix}\left(G, \mathrm{Real}\right) + t \cdot (\operatorname{Matrix}.\operatorname{single}\left(a, b, 1\right) + \operatorname{Matrix}.\operatorname{single}\left(b, a, 1\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.paramAdj` (`✓ std3`).

*Citation.* C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix (2023). *On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant*. DOI: [10.48550/arXiv.2211.01495](https://doi.org/10.48550/arXiv.2211.01495). URL: <https://arxiv.org/abs/2211.01495v2>.

*Commentary.*

Section 2, page 3, states: “Aksoy et al. in [2] represented M(t) = A + tB where A is the adjacency matrix of a graph G and B is a symmetric matrix representing a collection of edges.” It continues: “We will not restrict B and instead have B be a symmetric matrix representing any collection of edges denoted EC.” Section 1, page 3, states: “Here, we assume all unweighted edges have weight 1 and all non-edges have weight 0.” For vertices a and b, B is the sum of the two matrix units at (a,b) and (b,a); the vertex set is Fin n.

**Definition 1.2 (Normalized Laplacian).**

$$\forall n \in \mathrm{Nat},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathrm{Real}\right),\; \operatorname{normLap}\left(A\right) = 1 - \operatorname{Matrix}.\operatorname{of}\left(\operatorname{fun} i : \operatorname{Fin}\left(n\right) \mapsto \operatorname{fun} j : \operatorname{Fin}\left(n\right) \mapsto \frac{A\left(i, j\right)}{\operatorname{Real}.\operatorname{sqrt}\left(\sum_{k : \operatorname{Fin}\left(n\right)} A\left(i, k\right)\right) \cdot \operatorname{Real}.\operatorname{sqrt}\left(\sum_{k : \operatorname{Fin}\left(n\right)} A\left(j, k\right)\right)}\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.normLap` (`✓ std3`).

*Citation.* C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix (2023). *On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant*. DOI: [10.48550/arXiv.2211.01495](https://doi.org/10.48550/arXiv.2211.01495). URL: <https://arxiv.org/abs/2211.01495v2>.

*Commentary.*

Section 1, page 3, states: “The normalized Laplacian matrix of a graph is given by L = I − D^{−1/2} A D^{−1/2} where A is the adjacency matrix and D is the degree diagonal matrix.” The displayed entries use the row sums of A for those degrees, including for the perturbed adjacency matrix.

**Definition 1.3 (Kemeny's constant).**

$$\forall n \in \mathrm{Nat},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathrm{Real}\right),\; \operatorname{kemeny}\left(A\right) = \operatorname{Multiset}.\operatorname{sum}\left(\operatorname{Multiset}.\operatorname{map}\left(\operatorname{fun} x : \mathrm{Real} \mapsto x^{-1}, \operatorname{Multiset}.\operatorname{filter}\left(\operatorname{fun} x : \mathrm{Real} \mapsto x \ne 0, \operatorname{Polynomial}.\operatorname{roots}\left(\operatorname{Matrix}.\operatorname{charpoly}\left(\operatorname{normLap}\left(A\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.kemeny` (`✓ std3`).

*Citation.* C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix (2023). *On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant*. DOI: [10.48550/arXiv.2211.01495](https://doi.org/10.48550/arXiv.2211.01495). URL: <https://arxiv.org/abs/2211.01495v2>.

*Commentary.*

Section 1, page 3, states: “Kemeny’s constant can be computed as” K(G) = Σ_{λT ≠ 1} 1/(1 − λT) = Σ_{λL ≠ 0} 1/λL, “where each λL is an eigenvalue of L.” The encoding filters the multiset of real characteristic roots by nonzeroness, maps inversion, and sums. For the real symmetric normalized Laplacians in the proof, these roots are the eigenvalues with multiplicity.

**Definition 1.4 (Conjecture 3.5: minimality).**

$$\operatorname{claim} = (\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall a \in \operatorname{Fin}\left(n\right),\; \forall b \in \operatorname{Fin}\left(n\right),\; \forall dG \in \mathrm{Real},\; \forall dP \in \mathrm{Real},\; (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \Rightarrow ((a \ne b) \Rightarrow ((\operatorname{HasDerivAt}\left(\operatorname{fun} t : \mathrm{Real} \mapsto \operatorname{kemeny}\left(\operatorname{paramAdj}\left(G, a, b, t\right)\right), dG, 0\right)) \Rightarrow ((\operatorname{HasDerivAt}\left(\operatorname{fun} t : \mathrm{Real} \mapsto \operatorname{kemeny}\left(\operatorname{paramAdj}\left(\operatorname{SimpleGraph}.\operatorname{pathGraph}\left(n\right), \langle0\rangle, \langle n - 1\rangle, t\right)\right), dP, 0\right)) \Rightarrow (dP \le dG))))))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.claim` (`✓ std3`).

*Citation.* C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix (2023). *On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant*. DOI: [10.48550/arXiv.2211.01495](https://doi.org/10.48550/arXiv.2211.01495). URL: <https://arxiv.org/abs/2211.01495v2>.

*Commentary.*

Conjecture 3.5, page 19, states verbatim: “For a given n, the derivative of Kemeny’s constant on simple graphs of order n is smallest on the path on n vertices with respect to the non-edge connecting the ends of the path. The value of this derivative is O(n³).” The proposition expresses the first sentence for connected graphs on Fin n with n ≥ 2 and a ≠ b. Both derivatives must exist at zero. The path endpoints are the elements of Fin n with values 0 and n − 1; the inequality n ≥ 2 supplies their bounds. The second sentence concerns growth of the path value and is outside this proposition.

**Theorem 1.5 (A strict counterexample at order 23).**

$$\neg (\forall n \in \mathrm{Nat},\; (2 \le n) \Rightarrow (\forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall a \in \operatorname{Fin}\left(n\right),\; \forall b \in \operatorname{Fin}\left(n\right),\; \forall dG \in \mathrm{Real},\; \forall dP \in \mathrm{Real},\; (\operatorname{SimpleGraph}.\operatorname{Connected}\left(G\right)) \Rightarrow ((a \ne b) \Rightarrow ((\operatorname{HasDerivAt}\left(\operatorname{fun} t : \mathrm{Real} \mapsto \operatorname{kemeny}\left(\operatorname{paramAdj}\left(G, a, b, t\right)\right), dG, 0\right)) \Rightarrow ((\operatorname{HasDerivAt}\left(\operatorname{fun} t : \mathrm{Real} \mapsto \operatorname{kemeny}\left(\operatorname{paramAdj}\left(\operatorname{SimpleGraph}.\operatorname{pathGraph}\left(n\right), \langle0\rangle, \langle n - 1\rangle, t\right)\right), dP, 0\right)) \Rightarrow (dP \le dG))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/albright-et-al-2023-kemeny-edge-derivative-conjecture-3-5` (refuted) by `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"albright-et-al-2023-kemeny-edge-derivative-conjecture-3-5","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix (2023). *On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant*. DOI: [10.48550/arXiv.2211.01495](https://doi.org/10.48550/arXiv.2211.01495). URL: <https://arxiv.org/abs/2211.01495v2>.

*Commentary.*

Take cliques on {0,…,7} and {8,…,15}, joined by the path 0,16,17,18,19,20,21,22,8. This is a connected simple graph on Fin 23. The missing chord {0,8} has Kemeny derivative −7683669/4096 at zero, while the missing chord {0,22} of pathGraph 23 has derivative −77763/44. The difference is −4891047/45056 < 0. Grounded Green matrices give exact inverse certificates; spectral diagonalization identifies their weighted trace with the sum over nonzero characteristic roots. A rational rank-one update holds on a neighborhood of zero and yields both derivatives. Thus the universal minimality statement fails. No infinite family or asymptotic minimum is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.kemeny`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.normLap`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.paramAdj`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation.result`
