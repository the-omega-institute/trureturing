# Non-backtracking Laplacian gap

## Abstract

The non-backtracking transition spectrum has gap at most the reciprocal minimum-degree excess.

The source defines the non-backtracking graph on oriented edges and the random-walk Laplacian id minus D inverse times A. Its gap is the minimum norm of an eigenvalue of the transition matrix. The following Lean definitions use finite simple graphs on Fin n and the displayed transition weights.

**Definition 1.1 (Oriented edges).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; \operatorname{Arc}\left(G\right) = \operatorname{Subtype}\left(\operatorname{Prod}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right)\right), (p \mapsto \operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\left(\operatorname{Prod}.\operatorname{fst}\left(p\right), \operatorname{Prod}.\operatorname{snd}\left(p\right)\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.Arc` (`✓ std3`).

*Citation.* R. Mulas; D. Zhang; G. Zucal (2024). *There is no going back: Properties of the non-backtracking Laplacian*. DOI: [10.1016/j.laa.2023.10.014](https://doi.org/10.1016/j.laa.2023.10.014). URL: <https://arxiv.org/abs/2303.00373v2>.

*Commentary.*

For a graph G on Fin n, Arc G is the subtype of ordered vertex pairs whose endpoints are adjacent. These are the oriented edges used as states of the transition matrix.

**Definition 1.2 (Non-backtracking transition).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \forall a \in \operatorname{Arc}\left(G\right),\; \forall b \in \operatorname{Arc}\left(G\right),\; \operatorname{nbTransition}\left(G, a, b\right) = \operatorname{ite}\left(\operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(a\right)\right) = \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(b\right)\right) \land \left(\neg \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(b\right)\right) = \operatorname{Prod}.\operatorname{fst}\left(\operatorname{Subtype}.\operatorname{val}\left(a\right)\right)\right), \frac{1}{(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{SimpleGraph}.\operatorname{degree}\left(G, \operatorname{Prod}.\operatorname{snd}\left(\operatorname{Subtype}.\operatorname{val}\left(a\right)\right)\right)\right) : \mathrm{Real}) - 1}, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.nbTransition` (`✓ std3`).

*Citation.* R. Mulas; D. Zhang; G. Zucal (2024). *There is no going back: Properties of the non-backtracking Laplacian*. DOI: [10.1016/j.laa.2023.10.014](https://doi.org/10.1016/j.laa.2023.10.014). URL: <https://arxiv.org/abs/2303.00373v2>.

*Commentary.*

The transition from an arc [u,v] to an arc [v,w] has weight 1/(degree(v)-1) exactly when w is different from u; all other entries are zero.

**Definition 1.3 (Spectral gap).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] \operatorname{nbGap}\left(G\right) = \operatorname{sInf}\left(\{r : \mathrm{Real} \mid \exists mu \in \mathrm{Complex},\; mu \in \operatorname{spectrum}\left(\mathrm{Complex}, \operatorname{Matrix}.\operatorname{map}\left(\operatorname{nbTransition}\left(G\right), \operatorname{Algebra}.\operatorname{algebraMap}\left(\mathrm{Real}, \mathrm{Complex}\right)\right)\right) \land r = \left\lVert mu \right\rVert\}\right)$$

*Formalization.* `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.nbGap` (`✓ std3`).

*Citation.* R. Mulas; D. Zhang; G. Zucal (2024). *There is no going back: Properties of the non-backtracking Laplacian*. DOI: [10.1016/j.laa.2023.10.014](https://doi.org/10.1016/j.laa.2023.10.014). URL: <https://arxiv.org/abs/2303.00373v2>.

*Commentary.*

The gap is the infimum of the norms of the complex eigenvalues of the complexified transition matrix.

**Definition 1.4 (Conjecture 5.3).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] 0 < n \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{minDegree}\left(G\right) \ge 2 \Rightarrow \left(\left(\neg \operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(G, \operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(n\right)\right)\right)\right) \Rightarrow \operatorname{nbGap}\left(G\right) \le \frac{1}{(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{SimpleGraph}.\operatorname{minDegree}\left(G\right)\right) : \mathrm{Real}) - 1}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.claim` (`✓ std3`).

*Citation.* R. Mulas; D. Zhang; G. Zucal (2024). *There is no going back: Properties of the non-backtracking Laplacian*. DOI: [10.1016/j.laa.2023.10.014](https://doi.org/10.1016/j.laa.2023.10.014). URL: <https://arxiv.org/abs/2303.00373v2>.

*Commentary.*

The source states verbatim on printed page 16: “If G is not the cycle graph, then ε ≤ 1/(δ−1).” The encoding quantifies over finite simple graphs of positive order with minimum degree at least two, excludes graph isomorphism with the cycle graph, and uses nbGap G for ε.

**Theorem 1.5 (A nonzero eigenvector gives a spectral value).**

$$\forall iota \in \operatorname{Type}*,\; [\operatorname{Fintype}\left(iota\right)] [\operatorname{DecidableEq}\left(iota\right)] \forall A \in \operatorname{Matrix}\left(iota, iota, \mathrm{Complex}\right),\; \forall r \in \mathrm{Complex},\; \forall x \in iota \to \mathrm{Complex},\; \left(\neg x = 0\right) \Rightarrow \left(\operatorname{Matrix}.\operatorname{mulVec}\left(A, x\right) = \operatorname{HSMul}.\operatorname{hSMul}\left(r, x\right) \Rightarrow r \in \operatorname{spectrum}\left(\mathrm{Complex}, A\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.eigenpair_mem_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* R. Mulas; D. Zhang; G. Zucal (2024). *There is no going back: Properties of the non-backtracking Laplacian*. DOI: [10.1016/j.laa.2023.10.014](https://doi.org/10.1016/j.laa.2023.10.014). URL: <https://arxiv.org/abs/2303.00373v2>.

*Commentary.*

For any finite index type with decidable equality, a complex square matrix A, scalar r and nonzero vector x satisfying Matrix.mulVec A x = r • x, the scalar r belongs to spectrum ℂ A. The bound nbGap_le_norm_eigenpair uses this implication for the non-backtracking transition matrix.

**Theorem 1.6 (The non-backtracking gap bound).**

$$\forall n \in \mathrm{Nat},\; \forall G \in \operatorname{SimpleGraph}\left(\operatorname{Fin}\left(n\right)\right),\; [\operatorname{DecidableRel}\left(\operatorname{SimpleGraph}.\operatorname{Adj}\left(G\right)\right)] 0 < n \Rightarrow \left(\operatorname{SimpleGraph}.\operatorname{minDegree}\left(G\right) \ge 2 \Rightarrow \left(\left(\neg \operatorname{Nonempty}\left(\operatorname{SimpleGraph}.\operatorname{Iso}\left(G, \operatorname{SimpleGraph}.\operatorname{cycleGraph}\left(n\right)\right)\right)\right) \Rightarrow \operatorname{nbGap}\left(G\right) \le \frac{1}{(\operatorname{Nat}.\operatorname{cast}\left(\operatorname{SimpleGraph}.\operatorname{minDegree}\left(G\right)\right) : \mathrm{Real}) - 1}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.result` (`✓ std3`). ∎

*Resolves.* `Problems/mulas-zhang-zucal-2023-non-backtracking-gap-min-degree` (proved) by `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mulas-zhang-zucal-2023-non-backtracking-gap-min-degree","declaration_gid":"D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* R. Mulas; D. Zhang; G. Zucal (2024). *There is no going back: Properties of the non-backtracking Laplacian*. DOI: [10.1016/j.laa.2023.10.014](https://doi.org/10.1016/j.laa.2023.10.014). URL: <https://arxiv.org/abs/2303.00373v2>.

*Commentary.*

The result proves the quoted Conjecture 5.3. For minimum degree two, the all-ones vector is an eigenvector with eigenvalue one. For minimum degree at least three, the factorization P=RS with symmetric inverse factor T yields a Hermitian pencil T−tR; a dimension count and endpoint sign change give a singular t in [δ−1,Δ), hence a positive real transition eigenvalue at most 1/(δ−1). The cycle exclusion is therefore unnecessary.

## References

- Truth anchor: `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.Arc`
- Truth anchor: `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.claim`
- Truth anchor: `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.eigenpair_mem_spectrum`
- Truth anchor: `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.nbGap`
- Truth anchor: `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.nbTransition`
- Truth anchor: `D5/S3/Combinatorics/NonBacktracking/LaplacianGapMinDegree.result`
- Dependency: [D5/S3/Combinatorics/NonBacktracking/HermitianPencilCrossing](HermitianPencilCrossing.md)
