# Bell-type Riordan adjacency and the inertia question

## Abstract

An order-five Bell-type Riordan graph has positive inertia three and negative inertia two.

**Definition 1.1 (The source coefficient rule).**

$$\forall n \in \operatorname{Nat},\; \forall g \in \operatorname{PowerSeries}\left(\operatorname{Int}\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{adjacency}\left(n, g, i, j\right) = \operatorname{ite}\left(\operatorname{val}\left(j\right) < \operatorname{val}\left(i\right), (\operatorname{coeff}\left(\operatorname{val}\left(i\right) - 1, g \cdot (\operatorname{X} \cdot g)^{\operatorname{val}\left(j\right)}\right) \bmod 2: \operatorname{Real}), \operatorname{ite}\left(\operatorname{val}\left(i\right) < \operatorname{val}\left(j\right), (\operatorname{coeff}\left(\operatorname{val}\left(j\right) - 1, g \cdot (\operatorname{X} \cdot g)^{\operatorname{val}\left(i\right)}\right) \bmod 2: \operatorname{Real}), 0\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.adjacency` (`✓ std3`).

*Citation.* Gi-Sang Cheon, Ji-Hwan Jung, Sergey Kitaev and Seyed Ahmad Mojallal (2018). *Riordan graphs II: Spectral properties*. DOI: [10.1016/j.laa.2019.04.011](https://doi.org/10.1016/j.laa.2019.04.011). URL: <https://arxiv.org/abs/1801.07021v1>.

*Commentary.*

Definition 2.2 and equation (2), page 3, give r(i,j) congruent modulo 2 to the coefficient of z^(i-2) in g(z)f(z)^(j-1), for source labels 1 <= j < i <= n. Here f=X*g and i in Fin n denotes source label i.val+1. Thus the displayed natural subtraction val(i)-1 is exactly source i-2 on the lower triangle, and val(j) is source j-1. Lower(g,a,b) is expanded in the formula as the real cast of coeff(a-1, g*(X*g)^b) modulo positive two. This remainder is the unique integer in {0,1} congruent to the coefficient. The diagonal is zero and the upper triangle is reflected. The domain is the entire ring PowerSeries Int, with no polynomial degree bound. X*g has zero constant coefficient for every such g.

**Definition 1.2 (Problem 6.11 in full).**

$$\operatorname{claim} = (\forall n \in \operatorname{Nat},\; 1 \le n \Rightarrow \left(\forall g \in \operatorname{PowerSeries}\left(\operatorname{Int}\right),\; \operatorname{posIndex}\left(\operatorname{adjacency}\left(n, g\right)\right) \le \operatorname{negIndex}\left(\operatorname{adjacency}\left(n, g\right)\right)\right))$$

*Formalization.* `D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.claim` (`✓ std3`).

*Citation.* Gi-Sang Cheon, Ji-Hwan Jung, Sergey Kitaev and Seyed Ahmad Mojallal (2018). *Riordan graphs II: Spectral properties*. DOI: [10.1016/j.laa.2019.04.011](https://doi.org/10.1016/j.laa.2019.04.011). URL: <https://arxiv.org/abs/1801.07021v1>.

*Commentary.*

Problem 6.11, page 25: Is it true that n+ <= n- for any Riordan graph G_n(g,zg)? Every positive order n and every integer formal power series g is quantified. The displayed positive and negative indices are RHLinalg.posIndex and RHLinalg.negIndex applied to the canonical Hermitian proof for adjacency n g. They count eigenvalues strictly above and strictly below zero. Mathlib's Matrix.IsHermitian.roots_charpoly_eq_eigenvalues identifies the full indexed eigenvalue multiset with characteristic roots, so these are algebraic multiplicities and zero contributes to neither count. No properness, evenness, io-decomposability, nonsingularity or finite-order restriction is assumed.

**Theorem 1.3 (The order-five counterexample).**

$$\neg (\forall n \in \operatorname{Nat},\; 1 \le n \Rightarrow \left(\forall g \in \operatorname{PowerSeries}\left(\operatorname{Int}\right),\; \operatorname{posIndex}\left(\operatorname{adjacency}\left(n, g\right)\right) \le \operatorname{negIndex}\left(\operatorname{adjacency}\left(n, g\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/cheon-riordan-bell-inertia-611` (refuted) by `D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"cheon-riordan-bell-inertia-611","declaration_gid":"D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Gi-Sang Cheon, Ji-Hwan Jung, Sergey Kitaev and Seyed Ahmad Mojallal (2018). *Riordan graphs II: Spectral properties*. DOI: [10.1016/j.laa.2019.04.011](https://doi.org/10.1016/j.laa.2019.04.011). URL: <https://arxiv.org/abs/1801.07021v1>.

*Commentary.*

Set n=5 and g=1+X^3 in PowerSeries Int. Direct coefficient multiplication gives lower rows (1), (0,1), (0,0,1), (1,0,0,1), before reduction modulo two. The adjacency rows are (0,1,0,0,1), (1,0,1,0,0), (0,1,0,1,0), (0,0,1,0,1), (1,0,0,1,0). Let B have rows (1,1,-1,-1,1), (1,-1,0,0,-1), (0,0,1,1,-1), (0,0,1,-1,1), (0,0,0,0,1). Exact finite matrix arithmetic gives det B=4 and B transpose times A times B = diagonal(2,-2,2,-2,2). Apply D5.S3.Weil.Pick.InvertibleHermitianInertiaPullback.inertia_invariant_of_isUnit_det, then D5.S3.QuadraticForms.StructuredRankOneInertia.diagonal_counts. The indices are therefore 3 and 2, contradicting the universal inequality. The coefficient-to-adjacency equality is proved from the source series, rather than assumed from the cycle graph. The counterexample uses no restriction on the universal input domain.

## References

- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.adjacency`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/SpectralGraph/RiordanBellInertiaRefutation.result`
- Dependency: [D5/S3/QuadraticForms/StructuredRankOneInertia](../../QuadraticForms/StructuredRankOneInertia.md)
