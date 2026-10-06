# A bad Anderson potential without nontrivial shared symmetry

## Abstract

A potential on the eight-cycle has an eigenvector with a zero coordinate at every real coupling, while every matrix commuting with its Laplacian and potential is scalar. Thus no orthogonal shared symmetry other than I and -I exists.

**Definition 1.1 (Non-vanishing eigenvectors).**

$$\forall (L : \mathbb{N}), \forall (H : \operatorname{Matrix}\left(\operatorname{Fin}\left(L\right), \operatorname{Fin}\left(L\right), \mathbb{C}\right)), (\operatorname{nonvanishingEigenvectors}\left(H\right)) \Leftrightarrow (\forall (mu : \mathbb{C}), \forall (z : \operatorname{Fin}\left(L\right) \to \mathbb{C}), (z \ne 0) \Rightarrow ((\operatorname{Matrix.mulVec}\left(H, z\right) = mu \cdot (z)) \Rightarrow (\forall (j : \operatorname{Fin}\left(L\right)), z\left(j\right) \ne 0)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.nonvanishingEigenvectors` (`✓ std3`).

*Citation.* O. Lindblad and E. Guerrero (2025). *Simple Eigenvalues and Non-vanishing Eigenvectors of the Anderson Model*. URL: <https://arxiv.org/abs/2512.00278v1>.

*Commentary.*

Definition 1.1, page 2: "We say that V is a good potential if H_t = Δ + tV has simple eigenvalues and non-vanishing eigenvectors for all but finitely many t values." Every nonzero complex vector satisfying the eigenvector equation is quantified, and every vertex is required to have a nonzero coordinate. The zero vector is explicitly excluded. The notation *ᵥ is Matrix.mulVec and the scalar action is the usual complex scalar action.

**Definition 1.2 (Bad potentials).**

$$\forall (L : \mathbb{N}), \forall (v : \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\operatorname{bad}\left(v\right)) \Leftrightarrow (\forall (t : \mathbb{R}), \text{let} H : \operatorname{Matrix}\left(\operatorname{Fin}\left(L\right), \operatorname{Fin}\left(L\right), \mathbb{C}\right) := \operatorname{SimpleGraph.lapMatrix}\left(\mathbb{C}, \operatorname{SimpleGraph.cycleGraph}\left(L\right)\right) + \operatorname{Complex.ofReal}\left(t\right) \cdot (\operatorname{Matrix.diagonal}\left(\lambda (j : \operatorname{Fin}\left(L\right)), \operatorname{Complex.ofReal}\left(v\left(j\right)\right)\right)); \neg ((\forall (mu : \mathbb{C}), (\operatorname{Polynomial.IsRoot}\left(\operatorname{Matrix.charpoly}\left(H\right), mu\right)) \Rightarrow (\operatorname{Polynomial.rootMultiplicity}\left(mu, \operatorname{Matrix.charpoly}\left(H\right)\right) = 1)) \land (\operatorname{nonvanishingEigenvectors}\left(H\right))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.bad` (`✓ std3`).

*Citation.* O. Lindblad and E. Guerrero (2025). *Simple Eigenvalues and Non-vanishing Eigenvectors of the Anderson Model*. URL: <https://arxiv.org/abs/2512.00278v1>.

*Commentary.*

Definition 1.1, page 2: "We say that V is a bad potential if H_t fails to satisfy at least one of these conditions for any t ∈ ℝ." Here V is Matrix.diagonal v. Section 1, page 2, writes (H_t ψ)(j) = ∑_{k∼j}(ψ(j)−ψ(k)) + t ω_j ψ(j). The graph is Mathlib's SimpleGraph.cycleGraph L, whose adjacency for L > 2 is j−k = 1 or k−j = 1 in Fin L. Its lapMatrix acts by the literal sum of neighbour differences: lapMatrix_mulVec_apply gives degree times the coordinate minus the sum of neighbour coordinates. Both neighbours are distinct for L > 2. The potential and t are coerced from real to complex values in H; every real coupling is quantified. Simple eigenvalues are encoded literally by ∀ μ : ℂ, Polynomial.IsRoot (Matrix.charpoly H) μ → Polynomial.rootMultiplicity μ (Matrix.charpoly H) = 1. Every characteristic-polynomial root is required to have algebraic multiplicity one. Failure of the conjunction is exactly failure of at least one spectral condition.

**Definition 1.3 (Nontrivial shared symmetries).**

$$\forall (L : \mathbb{N}), \forall (v : \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\operatorname{sharedSymmetry}\left(v\right)) \Leftrightarrow (\exists (O : \operatorname{Matrix}\left(\operatorname{Fin}\left(L\right), \operatorname{Fin}\left(L\right), \mathbb{R}\right)), (O \in \operatorname{Matrix.orthogonalGroup}\left(\operatorname{Fin}\left(L\right), \mathbb{R}\right)) \land ((O \ne 1) \land ((O \ne -1) \land ((O \cdot \operatorname{SimpleGraph.lapMatrix}\left(\mathbb{R}, \operatorname{SimpleGraph.cycleGraph}\left(L\right)\right) = \operatorname{SimpleGraph.lapMatrix}\left(\mathbb{R}, \operatorname{SimpleGraph.cycleGraph}\left(L\right)\right) \cdot O) \land (O \cdot \operatorname{Matrix.diagonal}\left(v\right) = \operatorname{Matrix.diagonal}\left(v\right) \cdot O)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.sharedSymmetry` (`✓ std3`).

*Citation.* O. Lindblad and E. Guerrero (2025). *Simple Eigenvalues and Non-vanishing Eigenvectors of the Anderson Model*. URL: <https://arxiv.org/abs/2512.00278v1>.

*Commentary.*

Section 1, page 2: "To explain the discrepancy, in section 3 we show shared symmetries — orthogonal matrices that commute with both Δ and V — lead to the failure of our conditions." Matrix.orthogonalGroup is the real orthogonal group; membership is equivalent to OᵀO = I. The two scalar symmetries I and −I are excluded from nontriviality. This is the weak converse convention: either sufficient branch of Lemma 3.2, page 7, excludes −I, since (−I)² = I and −Ie_j ≠ e_j. Excluding both scalar matrices makes the question substantive while including every symmetry allowed by those branches.

**Definition 1.4 (The Lindblad–Guerrero converse).**

$$(claim) \Leftrightarrow (\forall (L : \mathbb{N}), (2 < L) \Rightarrow (\forall (v : \operatorname{Fin}\left(L\right) \to \mathbb{R}), (\forall (j : \operatorname{Fin}\left(L\right)), (v\left(j\right) = -1) \lor (v\left(j\right) = 1)) \Rightarrow ((\operatorname{bad}\left(v\right)) \Rightarrow (\operatorname{sharedSymmetry}\left(v\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.claim` (`✓ std3`).

*Citation.* O. Lindblad and E. Guerrero (2025). *Simple Eigenvalues and Non-vanishing Eigenvectors of the Anderson Model*. URL: <https://arxiv.org/abs/2512.00278v1>.

*Commentary.*

After Theorem 1.3, page 3: "Conversely, we also ask whether every bad potential shares a nontrivial symmetry with the laplacian." Section 4, page 8: "In general, we do not know whether the converse of lemma 3.2 is true." The displayed statement is the one-dimensional two-valued instance: every L > 2 and every labelled real potential taking values in {−1,1} is quantified. A counterexample in dimension one refutes the general-grid converse. Any two distinct values are obtained by αV + βI with α ≠ 0; H_t becomes H_{αt} + βtI, which shifts eigenvalues, preserves their multiplicities and preserves eigenvectors. Commutation with the potential is also unchanged by this affine transformation. Thus normalization to {−1,1} covers two-valued distributions.

**Theorem 1.5 (The eight-cycle refutation).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/lindblad-guerrero-2025-anderson-symmetry-converse-refutation` (refuted) by `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"lindblad-guerrero-2025-anderson-symmetry-converse-refutation","declaration_gid":"D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* O. Lindblad and E. Guerrero (2025). *Simple Eigenvalues and Non-vanishing Eigenvectors of the Anderson Model*. URL: <https://arxiv.org/abs/2512.00278v1>.

*Commentary.*

Take v = (1,1,1,1,−1,1,−1,−1). For any real t, put a = √(t²+2)−t. Then a²+2ta−2 = 0, and z = (1,0,−1,a,1−a²,−2t,1,−a) is an eigenvector with eigenvalue 2+a+t = 2+√(t²+2). Its first coordinate is 1 and its coordinate of index 1 is 0, so it is nonzero and violates non-vanishing for every t. To exclude shared symmetries, the finite Laplacian is evaluated exactly. Rational linear combinations of its commutator equations and those of Matrix.diagonal v give O = (O 0 0) • I for every real commuting matrix O. Orthogonality then gives (O 0 0)² = 1, so O is I or −I. The bad potential therefore has no nontrivial shared symmetry.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.bad`
- Truth anchor: `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.nonvanishingEigenvectors`
- Truth anchor: `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Graph/AndersonSymmetryConverseRefutation.sharedSymmetry`
