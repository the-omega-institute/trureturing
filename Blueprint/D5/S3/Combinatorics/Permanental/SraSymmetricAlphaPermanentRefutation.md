# Sra: symmetric alpha-permanent assertion

## Abstract

Symmetry of an inverse M matrix does not force log-supermodularity of every positive-order alpha-permanent.

**Definition 1.1 (Symmetrizable).**

$$\forall n \in \mathbb {N},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{Symmetrizable}\left(A\right)) \Leftrightarrow (\exists delta \in \operatorname{Fin}\left(n\right) \to \mathbb {R},\; (\forall i \in \operatorname{Fin}\left(n\right),\; 0 < delta\left(i\right)) \land (\operatorname{Matrix}.\operatorname{IsSymm}\left(\operatorname{Matrix}.\operatorname{diagonal}\left(delta\right) \cdot A \cdot \operatorname{Matrix}.\operatorname{diagonal}\left(fun (i : \operatorname{Fin}\left(n\right)) \mapsto delta\left(i\right)^{-1}\right)\right)))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.Symmetrizable` (`✓ std3`).

*Citation.* Suvrit Sra (2026). *A Koteljanskii inequality for permanents*. DOI: [10.48550/arXiv.2609.39979](https://doi.org/10.48550/arXiv.2609.39979). URL: <https://arxiv.org/abs/2609.39979v1>.

*Commentary.*

Source, p. 1: “We prove (1.1) for inverse M-matrices that are symmetric after a positive diagonal similarity, which we call symmetrizable, and show that (1.1) can fail without this hypothesis.” The positive function delta gives that diagonal similarity.

**Definition 1.2 (alphaPermanent).**

$$\forall I \in Type*,\; [\operatorname{Fintype}\left(I\right)] [\operatorname{DecidableEq}\left(I\right)] \forall alpha \in \mathbb {R},\; \forall H \in \operatorname{Matrix}\left(I, I, \mathbb {R}\right),\; \operatorname{alphaPermanent}\left(alpha, H\right) = (\sum_{pi:\operatorname{Equiv}.\operatorname{Perm}\left(I\right)} (alpha^{\operatorname{Multiset}.\operatorname{card}\left(\operatorname{cycleType}\left(pi\right)\right) + \operatorname{Finset}.\operatorname{card}\left(\operatorname{Finset}.\operatorname{filter}\left(fun (i : I) \mapsto pi\left(i\right) = i, univ\right)\right)} \cdot (\prod_{i:I} (H\left(i, pi\left(i\right)\right)))))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.alphaPermanent` (`✓ std3`).

*Citation.* Suvrit Sra (2026). *A Koteljanskii inequality for permanents*. DOI: [10.48550/arXiv.2609.39979](https://doi.org/10.48550/arXiv.2609.39979). URL: <https://arxiv.org/abs/2609.39979v1>.

*Commentary.*

Source, p. 5, equation (3.1): “For α>0, the α-permanent of a matrix H indexed by S is” the permutation sum, “where 𝔖(S) is the group of permutations of S and c(π) is the number of cycles of π; the ordinary permanent is α=1.” The exponent adds nontrivial cycles and fixed points, including one-cycles; the empty permutation gives one.

**Definition 1.3 (principalAlphaPermanent).**

$$\forall n \in \mathbb {N},\; \forall alpha \in \mathbb {R},\; \forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; \forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{principalAlphaPermanent}\left(alpha, A, S\right) = \operatorname{alphaPermanent}\left(alpha, \operatorname{Matrix}.\operatorname{submatrix}\left(A, fun (i : S) \mapsto \operatorname{val}\left(i\right), fun (j : S) \mapsto \operatorname{val}\left(j\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.principalAlphaPermanent` (`✓ std3`).

*Citation.* Suvrit Sra (2026). *A Koteljanskii inequality for permanents*. DOI: [10.48550/arXiv.2609.39979](https://doi.org/10.48550/arXiv.2609.39979). URL: <https://arxiv.org/abs/2609.39979v1>.

*Commentary.*

Source, p. 1: “For an n×n matrix A and S⊆[n], write A_S=A[S,S] for the principal submatrix with row and column set S, and set det(A_∅)=per(A_∅)=1.” Here Matrix.submatrix uses the subtype S and val denotes its underlying Fin n index; the same restriction is used for the alpha-permanent.

**Definition 1.4 (claim).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb {N},\; (0 < n) \Rightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{SraReciprocalPermanentLorentzianRefutation}.\operatorname{InverseMMatrix}\left(A\right)) \Rightarrow ((\operatorname{Symmetrizable}\left(A\right)) \Rightarrow (\forall alpha \in \mathbb {R},\; (0 < alpha) \Rightarrow ((alpha \ne \frac{1}{2}) \Rightarrow ((alpha \ne 1) \Rightarrow (\forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{principalAlphaPermanent}\left(alpha, A, S\right) \cdot \operatorname{principalAlphaPermanent}\left(alpha, A, T\right) \le \operatorname{principalAlphaPermanent}\left(alpha, A, \operatorname{Finset}.\operatorname{union}\left(S, T\right)\right) \cdot \operatorname{principalAlphaPermanent}\left(alpha, A, \operatorname{Finset}.\operatorname{inter}\left(S, T\right)\right))))))))$$

*Formalization.* `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.claim` (`✓ std3`).

*Citation.* Suvrit Sra (2026). *A Koteljanskii inequality for permanents*. DOI: [10.48550/arXiv.2609.39979](https://doi.org/10.48550/arXiv.2609.39979). URL: <https://arxiv.org/abs/2609.39979v1>.

*Commentary.*

Source, p. 6, §4(b): “For symmetrizable inverse M-matrices and α∉{½,1}, decide whether S↦per_α(A_S) is log-supermodular.” Alpha is positive as in equation (3.1). The formula is the universal affirmative assertion, with both distinguished positive orders excluded. Fin n index i represents source index i+1, and S,T range over finite subsets of those indices.

**Theorem 1.5 (result).**

$$\neg (\forall n \in \mathbb {N},\; (0 < n) \Rightarrow (\forall A \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb {R}\right),\; (\operatorname{SraReciprocalPermanentLorentzianRefutation}.\operatorname{InverseMMatrix}\left(A\right)) \Rightarrow ((\operatorname{Symmetrizable}\left(A\right)) \Rightarrow (\forall alpha \in \mathbb {R},\; (0 < alpha) \Rightarrow ((alpha \ne \frac{1}{2}) \Rightarrow ((alpha \ne 1) \Rightarrow (\forall S \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \forall T \in \operatorname{Finset}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{principalAlphaPermanent}\left(alpha, A, S\right) \cdot \operatorname{principalAlphaPermanent}\left(alpha, A, T\right) \le \operatorname{principalAlphaPermanent}\left(alpha, A, \operatorname{Finset}.\operatorname{union}\left(S, T\right)\right) \cdot \operatorname{principalAlphaPermanent}\left(alpha, A, \operatorname{Finset}.\operatorname{inter}\left(S, T\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/sra2609-symmetric-alpha-permanent` (refuted) by `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"sra2609-symmetric-alpha-permanent","declaration_gid":"D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Suvrit Sra (2026). *A Koteljanskii inequality for permanents*. DOI: [10.48550/arXiv.2609.39979](https://doi.org/10.48550/arXiv.2609.39979). URL: <https://arxiv.org/abs/2609.39979v1>.

*Commentary.*

The symmetric matrix with rows (7,2,1,2), (2,7,2,1), (1,2,7,2), (2,1,2,7) is entrywise positive and inverse M. For S={0,1,2} and T={0,2,3}, the union-intersection product minus the S,T product equals alpha²(alpha+1)(2401alpha²+1617alpha−16), which is negative throughout 0<alpha≤1/200. Taking alpha=1/200 refutes the assertion.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.Symmetrizable`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.alphaPermanent`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.principalAlphaPermanent`
- Truth anchor: `D5/S3/Combinatorics/Permanental/SraSymmetricAlphaPermanentRefutation.result`
- Dependency: [D5/S3/Combinatorics/Permanental/SraReciprocalPermanentLorentzianRefutation](SraReciprocalPermanentLorentzianRefutation.md)
