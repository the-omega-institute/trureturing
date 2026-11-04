# New Laplacian layer maxima decrease on the four-vertex star

## Abstract

For the actual connected star on four vertices, the first two new Laplacian layers have maxima 4 and 3. Their decrease refutes the whole successive-layer monotonicity conjecture.

**Definition 1.1 (The complete ordinary Laplacian spectral multiset).**

$$\operatorname{spectrum}\left(G\right) = \operatorname{map}\left(\operatorname{eigenvalues}\left(\operatorname{lapMatrix}\left(G, \mathbb{R}\right)\right), \operatorname{univ}\left(V\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.spectrum` (`✓ std3`).

*Citation.* M. A. Reyes and C. Dalfó and M. À. Fiol (2024). *On the spectra and spectral radii of token graphs*. DOI: [10.1007/s40590-023-00583-3](https://doi.org/10.1007/s40590-023-00583-3). URL: <https://arxiv.org/html/2310.16929v1>.

*Commentary.*

For any finite vertex type V with decidable equality and finite simple graph G with decidable adjacency, spectrum maps every eigenvalue index to the real eigenvalue of the Hermitian degree-minus-adjacency matrix. It retains every algebraic multiplicity. Matrix.IsHermitian.roots_charpoly_eq_eigenvalues identifies exactly this multiset with the roots of the characteristic polynomial; this identity is applied in spectrum_from_basis. It is neither the set-valued spectrum nor an adjacency spectrum.

**Definition 1.2 (Consecutive multiset subtraction).**

$$\operatorname{layer}\left(G, k\right) = \operatorname{spectrum}\left(\operatorname{tokenGraph}\left(G, k\right)\right) - \operatorname{spectrum}\left(\operatorname{tokenGraph}\left(G, k-1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.layer` (`✓ std3`).

*Citation.* M. A. Reyes and C. Dalfó and M. À. Fiol (2024). *On the spectra and spectral radii of token graphs*. DOI: [10.1007/s40590-023-00583-3](https://doi.org/10.1007/s40590-023-00583-3). URL: <https://arxiv.org/html/2310.16929v1>.

*Commentary.*

The existing tokenGraph uses Set.powersetCard, not a preassigned graph or matrix: its vertices are all k-element finite subsets, and its two directed singleton differences form an edge of G. For equal-size subsets these singleton differences are equivalent to the source symmetric-difference condition. Multiset subtraction removes the previous multiplicity of each eigenvalue. F_0 is the one empty subset, so its Laplacian has spectrum {0}. Only after this subtraction does rho convert to a finite set to take a maximum.

**Definition 1.3 (The maximum on the full nonempty source domain).**

$$\operatorname{rho}\left(G, k\right) = \operatorname{maxPrime}\left(\operatorname{toFinset}\left(\operatorname{layer}\left(G, k\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.rho` (`✓ std3`).

*Citation.* M. A. Reyes and C. Dalfó and M. À. Fiol (2024). *On the spectra and spectral radii of token graphs*. DOI: [10.1007/s40590-023-00583-3](https://doi.org/10.1007/s40590-023-00583-3). URL: <https://arxiv.org/html/2310.16929v1>.

*Commentary.*

Definition 3.1: for 1 ≤ k ≤ floor(n/2), rho is the maximum eigenvalue in the consecutive spectral multiset difference. The Lean arguments hk and hkn prove these bounds. The consumed helper layer_nonempty proves nonemptiness for every n and every graph in this range: the two complete spectral multisets have cardinalities choose(n,k) and choose(n,k−1); the binomial recurrence and k ≤ n/2 give a strict increase. A zero multiset difference would imply the opposite cardinal inequality. Thus no nonemptiness assumption or default numeric value replaces any source case.

**Definition 1.4 (The entire original Conjecture 3.3).**

$$claim \Leftrightarrow \forall (n: \mathbb{N}), \forall (G: \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right)), [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall (k: \mathbb{N}), \left(1 \le k \land k < \operatorname{div}\left(n, 2\right)\right) \Rightarrow \operatorname{rho}\left(G, k\right) \le \operatorname{rho}\left(G, k+1\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.claim` (`✓ std3`).

*Citation.* M. A. Reyes and C. Dalfó and M. À. Fiol (2024). *On the spectra and spectral radii of token graphs*. DOI: [10.1007/s40590-023-00583-3](https://doi.org/10.1007/s40590-023-00583-3). URL: <https://arxiv.org/html/2310.16929v1>.

*Commentary.*

Conjecture 3.3 states: For any graph G, ρ₁(G) ≤ ρ₂(G) ≤ ⋯ ≤ ρ⌊n/2⌋(G). The formal claim quantifies every n, every simple unweighted undirected graph on Fin n with decidable adjacency, and every 1 ≤ k < n/2, where division is natural-number division. Fin n provides all finite labelled graphs of every order. The bounds supplied to rho at k and k+1 are proved from this range. There is no graph-order cap, fixed-graph restriction, spectral-containment premise, replacement by full radii, or conclusion assumed as a hypothesis. The source's introductory connected-graph convention is also met by the counterexample: connectedStar stores the actual star with Mathlib's connected_starGraph proof.

**Theorem 1.5 (A connected exact counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/reyes-dalfo-fiol-2024-new-laplacian-layer-maxima` (refuted) by `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"reyes-dalfo-fiol-2024-new-laplacian-layer-maxima","declaration_gid":"D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* M. A. Reyes and C. Dalfó and M. À. Fiol (2024). *On the spectra and spectral radii of token graphs*. DOI: [10.1007/s40590-023-00583-3](https://doi.org/10.1007/s40590-023-00583-3). URL: <https://arxiv.org/html/2310.16929v1>.

*Commentary.*

Take K₁,₃ on Fin 4 with center 0. The equivalences e0, e1, e2 enumerate all actual token subsets, with e2 in the order 01,12,02,23,03,13. Decidable integer Laplacian identities verify every degree and adjacency entry. In particular the two-token matrix is the ordinary C₆ Laplacian, with two neighbors at every vertex and no extra edges. Entrywise casting preserves these actual matrices over the reals. The displayed rational matrices P and Q in spectrum1 and spectrum2 satisfy QP=I and LP=P diag(d), so their columns form complete eigenbases, not merely lists of eigenvectors. Mathlib's characteristic-polynomial identities and Hermitian roots theorem then prove the entire spectral multisets: Sp₀={0}, Sp₁={0,1,1,4}, Sp₂={0,1,1,3,3,4}. Exact multiset subtraction gives Δ₁={1,1,4} and Δ₂={3,3}; Finset.max' gives ρ₁=4 and ρ₂=3. At n=4,k=1 the original universal claim requires 4≤3, a contradiction.

The star and six-cycle spectral ingredients occur in Dongsheng Wei, arXiv:2609.26802v1 Section 4.6 and v2 Section 7, as recorded in the source note. This calculation applies those ingredients to the consecutive new-layer multisets. Full Laplacian maxima remain 4 at both positive levels, whereas the new-layer maxima decrease. Conjecture 3.2 about minima and the separate full-radius equality characterization concern different statements.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.layer`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.rho`
- Truth anchor: `D5/S3/Combinatorics/Graph/TokenGraph/NewLayerMaximaRefutation.spectrum`
- Dependency: [D5/S3/Combinatorics/Graph/TokenGraphLaplacianRadiusRefutation](../TokenGraphLaplacianRadiusRefutation.md)
