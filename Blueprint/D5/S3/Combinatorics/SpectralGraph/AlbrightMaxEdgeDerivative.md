# The maximum normalized Laplacian edge derivative

## Abstract

The normalized Laplacian edge derivative has sharp upper bound one.

**Definition 1.1 (Full normalized Laplacian eigenspace).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.eigenspace`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.eigenspace` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix (2023). *On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant*. DOI: [10.48550/arXiv.2211.01495](https://doi.org/10.48550/arXiv.2211.01495). URL: <https://arxiv.org/abs/2211.01495v2>.

*Commentary.*

At t = 0 the frozen one-pair perturbation is the ordinary unweighted adjacency. The frozen normalized Laplacian acts on real Euclidean vertex space. The eigenspace is the entire kernel of L(0) minus the given eigenvalue times the identity.

**Definition 1.2 (Normalized trace on the fixed eigenspace).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.rayleighAverage`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.rayleighAverage` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix (2023). *On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant*. DOI: [10.48550/arXiv.2211.01495](https://doi.org/10.48550/arXiv.2211.01495). URL: <https://arxiv.org/abs/2211.01495v2>.

*Commentary.*

For an orthonormal basis of the entire eigenspace with k elements, sum the fixed-vector Rayleigh forms uᵀ L(t) u and divide by k. The vectors are fixed at t = 0. Compressing L(t) by orthogonal projection onto this eigenspace identifies the sum with its trace at each t.

**Definition 1.3 (The derivative in Lemma 2.3).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.edgeDerivative`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.edgeDerivative` (`✓ std3`).

*Citation.* C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix (2023). *On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant*. DOI: [10.48550/arXiv.2211.01495](https://doi.org/10.48550/arXiv.2211.01495). URL: <https://arxiv.org/abs/2211.01495v2>.

*Commentary.*

Lemma 2.3, equation (2.3), averages over the k elements of an orthonormal basis for the eigenvalue λ. For a single distinct pair x,y and a basis vector u, put s = 1 − λ and gᵢ = uᵢ/√dᵢ. The summand is s(gₓ² + gᵧ²) − 2gₓgᵧ. For positive degrees this equals the displayed source expression with denominators dₓ, dᵧ and √(dₓdᵧ). The same definition covers edges and nonedges.

**Definition 1.4 (Conjecture 2.20).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.claim`

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.claim` (`✓ std3`).

*Citation.* C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix (2023). *On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant*. DOI: [10.48550/arXiv.2211.01495](https://doi.org/10.48550/arXiv.2211.01495). URL: <https://arxiv.org/abs/2211.01495v2>.

*Commentary.*

Conjecture 2.20 states that over all graphs the maximum edge derivative for any pair of vertices is 1. The universal clause ranges over every finite connected simple unweighted graph of order at least two, every distinct pair, and every real normalized Laplacian eigenvalue of positive multiplicity. The basis has type OrthonormalBasis on the full eigenspace, so k is its dimension. For each such basis, the source formula is the derivative of the normalized compressed trace at zero, is basis-independent and is at most 1. The attaining graph is the connected path on three vertices, with the nonedge joining its endpoints and the one-dimensional eigenspace at eigenvalue 1.

**Theorem 1.5 (The attained maximum is one).**

Lean statement: `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.result` (`✓ std3`). ∎

*Resolves.* `Problems/albright-et-al-2023-max-edge-derivative-conjecture-2-20` (proved) by `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"albright-et-al-2023-max-edge-derivative-conjecture-2-20","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. Albright; K. P. Hadaway; A. H. Pomerance; J. Jeffries; K. J. Lorenzen; A. K. Nix (2023). *On the Edge Derivative of the Normalized Laplacian with Applications to Kemeny's Constant*. DOI: [10.48550/arXiv.2211.01495](https://doi.org/10.48550/arXiv.2211.01495). URL: <https://arxiv.org/abs/2211.01495v2>.

*Commentary.*

The perturbation adds t to the two opposite adjacency entries. The degree row sums increase by t at each endpoint. Write P = D⁻¹ᐟ² and B = PAP at zero. Differentiating each reciprocal square root gives L′ = (HB + BH)/2 − PCP, where C is the perturbation matrix and H has diagonal dᵢ′/dᵢ. On an s-eigenvector of B, the resulting quadratic form is the Lemma 2.3 summand. The trace identity and derivative uniqueness give independence of basis.

The ordinary graph Laplacian and the sum of squares over ordered adjacent pairs give the inequalities for I − B and I + B. Thus −1 ≤ s ≤ 1. Completing a square bounds the summand by (1 + s)(gₓ² + gᵧ²). If s ≤ 0, degrees are at least one and the endpoint mass is at most one. For s > 0 and adjacent endpoints with degrees at least two, the scaled endpoint mass is at most one half. At a leaf on an adjacent pair, the eigenvector equation gives gᵧ = s gₓ after labelling the leaf x, and the summand is nonpositive.

For a nonedge let w be u restricted to x and y, and let m = uₓ² + uᵧ². Then wᵀBw = 0 and wᵀu = wᵀw = m. Evaluating the quadratic form of I + B on w − mu gives m − (1 + s)m² ≥ 0. With m > 0 this yields (1 + s)m ≤ 1. The case m = 0 gives a zero summand. Every basis vector therefore contributes at most one, so the average has the same bound for every positive multiplicity.

For the path on three vertices, the unit vector (1,0,−1)/√2 spans the eigenspace at 1. The perturbed normalized Laplacian on this vector has eigenvalue 1 + t/(1 + t) near zero. Its derivative at zero is 1.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.edgeDerivative`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.eigenspace`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.rayleighAverage`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/AlbrightMaxEdgeDerivative.result`
- Dependency: [D5/S3/Combinatorics/SpectralGraph/AlbrightKemenyEdgeDerivativeRefutation](AlbrightKemenyEdgeDerivativeRefutation.md)
