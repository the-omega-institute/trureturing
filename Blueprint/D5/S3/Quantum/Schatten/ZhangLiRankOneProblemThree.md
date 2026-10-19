# Zhang–Li Problem 3 for matrices of rank at most one

## Abstract

Zhang–Li Problem 3 for matrices of rank at most one.

Lei-Hong Zhang and Ren-Cang Li, On a Conjecture Related to Eigenvalue Perturbations, arXiv:2609.25552v1, §1 Problem 3 and §5.

Problem 3: Relate min_{W nonsingular} ‖W∘G‖_ui ‖W^{-1}∘G^T‖_ui to min_{P permutation} ‖P∘G‖_ui^2.

In fact, for rank-one G, Romeo and Tilli [23, Theorem 1.2] proved (1.1) with c1=1 and the unitary restriction (2.3) with c2=1. They explicitly left the corresponding nonsingular version of Problem 3 unresolved; see [23, Remark 3.1].

Zhang–Li Theorem 1.1 proves Conjecture 1.1 with c = 1 for the Frobenius norm for every G. The result here settles the rank-at-most-one case for every unitarily invariant norm. Higher rank remains open for general unitarily invariant norms; the Frobenius case is already solved by Zhang–Li.

The averaging method has a related precedent in R. Bhatia, F. Kittaneh, R.-C. Li, Some inequalities for commutators and an application to spectral variation. II, Linear and Multilinear Algebra 43 (1997), no. 1–3, 207–219, §4, https://doi.org/10.1080/03081089708818526. The exact remark number is ASSUMED-UNVERIFIED.

**Definition 1.1 (The complete rank-one variational assertion).**

Lean statement: `D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree.claim`

*Formalization.* `D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree.claim` (`✓ std3`).

*Citation.* Lei-Hong Zhang and Ren-Cang Li (2026). *On a Conjecture Related to Eigenvalue Perturbations*. DOI: [10.48550/arXiv.2609.25552](https://doi.org/10.48550/arXiv.2609.25552). URL: <https://arxiv.org/abs/2609.25552>.

*Commentary.*

For every natural n, every complex n by n matrix G of rank at most one, and every unitarily invariant norm N, there exists a permutation σ minimizing N(Pσ∘G) over all permutations, with N(Pσ∘G)²≤N(W∘G)N(W⁻¹∘Gᵀ) for every invertible W and equality in that product when W=Pσ. This includes zero G and dimension zero.

**Theorem 1.2 (The rank-one infimum equals the permutation minimum).**

Lean statement: `D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree.result`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-li-2026-rank-one-hadamard-product-variational` (proved) by `D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-li-2026-rank-one-hadamard-product-variational","declaration_gid":"D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For every natural n, every complex n by n G of rank at most one and every unitarily invariant norm N, the infimum over invertible W of N(W∘G)N(W⁻¹∘Gᵀ) equals the minimum over permutation matrices P of N(P∘G)², attained at a minimizing permutation. The statement supplies that permutation together with the lower bound for every invertible W and the equality at the permutation. Factor G and remove its phases to obtain common nonnegative diagonal weights. The expanding diagonal minimum bounds every balanced inverse-adjoint average, and optimization over its positive scale gives the product bound.

## References

- Truth anchor: `D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree.claim`
- Truth anchor: `D5/S3/Quantum/Schatten/ZhangLiRankOneProblemThree.result`
- Dependency: [D5/S3/Quantum/Schatten/ExpandingAverage](ExpandingAverage.md)
- Dependency: [D5/S3/Quantum/Schatten/ExpandingDiagonal](ExpandingDiagonal.md)
- Dependency: [D5/S3/Quantum/Schatten/ExpandingNormProduct](ExpandingNormProduct.md)
- Dependency: [D5/S3/Quantum/Schatten/RankOneHadamard](RankOneHadamard.md)
- Dependency: [D5/S3/Quantum/Schatten/UnitarilyInvariantNorm](UnitarilyInvariantNorm.md)
