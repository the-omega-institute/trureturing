# The discriminant clears average mixing denominators

## Abstract

For every finite simple graph, the discriminant of the rational minimal polynomial of its adjacency matrix times its average mixing matrix has integer entries.

**Definition 1.1 (Godsil's Question 1).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \exists z \in \mathbb{Z},\; \operatorname{algebraMap}\left(\mathbb{Q}, \mathbb{R}, \operatorname{discr}\left(\operatorname{minpoly}\left(\mathbb{Q}, \operatorname{adjMatrix}\left(\mathbb{Q}, G\right)\right)\right)\right) \cdot \operatorname{avgMixing}\left(G, i, j\right) = \operatorname{algebraMap}\left(\mathbb{Z}, \mathbb{R}, z\right))$$

*Formalization.* `D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.claim` (`✓ std3`).

*Citation.* Chris Godsil (2013). *Average mixing of continuous quantum walks*. DOI: [10.1016/j.jcta.2013.05.006](https://doi.org/10.1016/j.jcta.2013.05.006). URL: <https://arxiv.org/abs/1103.2578v3>.

*Commentary.*

C. Godsil, Average Mixing of Continuous Quantum Walks, arXiv:1103.2578v3, section 11, Question 1 (page 20), asks: "Is it true that if D is the discriminant of the minimal polynomial of X, then $D \widehat{M}_{X}$ is an integer matrix?" Here X is encoded by a simple graph G on Fin n with decidable adjacency; minpoly is taken over the rationals and discr is Polynomial.discr. The real coercions of the rational discriminant and the integer z are displayed explicitly. The average mixing matrix is the source's Lemma 1.1 form (page 3), the sum of the Schur squares of the orthogonal spectral projections over the distinct eigenvalues, as in AverageMixingTraceMaximum.avgMixing. There is no connectedness or simple-spectrum hypothesis. Mathlib assigns discriminant 1 to degree-one and constant polynomials; when n = 0 there are no entry indices.

**Theorem 1.2 (An affirmative answer).**

$$\forall n \in \mathbb{N},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{Adj}\left(G\right)\right)], \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \exists z \in \mathbb{Z},\; \operatorname{algebraMap}\left(\mathbb{Q}, \mathbb{R}, \operatorname{discr}\left(\operatorname{minpoly}\left(\mathbb{Q}, \operatorname{adjMatrix}\left(\mathbb{Q}, G\right)\right)\right)\right) \cdot \operatorname{avgMixing}\left(G, i, j\right) = \operatorname{algebraMap}\left(\mathbb{Z}, \mathbb{R}, z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.result` (`✓ std3`). ∎

*Resolves.* `Problems/godsil-2011-average-mixing-discriminant-integrality` (proved) by `D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"godsil-2011-average-mixing-discriminant-integrality","declaration_gid":"D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chris Godsil (2013). *Average mixing of continuous quantum walks*. DOI: [10.1016/j.jcta.2013.05.006](https://doi.org/10.1016/j.jcta.2013.05.006). URL: <https://arxiv.org/abs/1103.2578v3>.

*Commentary.*

Write the squarefree minimal polynomial as the product of the factors t minus theta over the distinct eigenvalues. For each theta let q_theta be the product with that factor deleted. Polynomial evaluation at the adjacency matrix gives q_theta(A) = q_theta(theta) E_theta. The resultant identity disc((t - theta) q_theta) = disc(q_theta) q_theta(theta)^2 cancels the squared spectral denominator. Thus each entry of D times the average mixing matrix is the sum over theta of disc(q_theta) times the square of the corresponding entry of q_theta(A). This sum is an integer polynomial in the distinct eigenvalues and is invariant under their permutations. The fundamental theorem of symmetric polynomials expresses it as an integer polynomial in the elementary symmetric functions; Vieta identifies these with signed coefficients of the monic integer minimal polynomial. Consequently every scaled entry is an integer. The argument sharpens the D squared bound in Lemma 3.1 to D.

## References

- Truth anchor: `D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.claim`
- Truth anchor: `D5/S3/Quantum/Dynamics/AverageMixingDiscriminantIntegrality.result`
- Dependency: [D5/S3/Quantum/Dynamics/AverageMixingTraceMaximum](AverageMixingTraceMaximum.md)
