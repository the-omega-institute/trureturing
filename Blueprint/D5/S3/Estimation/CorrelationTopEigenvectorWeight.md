# Top eigenvector weights on the remaining correlation domain

## Abstract

On the remaining correlation domain, matrices whose top eigenvectors have smaller weight exist in every sufficiently large dimension exactly when c is less than sigma.

**Definition 1.1 (Correlation matrices).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(c: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.IsCorrelation}\left(c\right)\right) \Leftrightarrow \left(\left(\operatorname{Matrix.PosSemidef}\left(c\right)\right) \land \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(c\left(i, i\right) = \left(1: \mathbb{R}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Estimation/CorrelationTopEigenvectorWeight.IsCorrelation` (`✓ std3`).

*Citation.* Yuriy Stepanov; Hendrik Herrmann; Thomas Guhr (2021). *Generic features in the spectral decomposition of correlation matrices*. DOI: [10.1063/5.0054438](https://doi.org/10.1063/5.0054438). URL: <https://arxiv.org/abs/2104.08966v1>.

*Commentary.*

A real matrix is a correlation matrix when it is positive semidefinite and every diagonal entry is one. Matrix.PosSemidef includes symmetry over the real scalars. These are conditions (i)–(iii) in the source's TeX, lines 141–146. The predicate is defined for every natural dimension, including zero.

**Definition 1.2 (Mean off-diagonal correlation).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(c: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.meanCorr}\left(c\right): \mathbb{R}\right) = \left(\frac{2}{\left(\left(\operatorname{Nat.cast}\left(n\right): \mathbb{R}\right)\right) \cdot \left(\left(\left(\operatorname{Nat.cast}\left(n\right): \mathbb{R}\right)\right) - \left(1\right)\right)}\right) \cdot \left(\sum_{\left(i: \operatorname{Fin}\left(n\right)\right)} \left(\sum_{\left(j: \operatorname{Fin}\left(n\right)\right), j < i} \left(c\left(i, j\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Estimation/CorrelationTopEigenvectorWeight.meanCorr` (`✓ std3`).

*Citation.* Yuriy Stepanov; Hendrik Herrmann; Thomas Guhr (2021). *Generic features in the spectral decomposition of correlation matrices*. DOI: [10.1063/5.0054438](https://doi.org/10.1063/5.0054438). URL: <https://arxiv.org/abs/2104.08966v1>.

*Commentary.*

The mean is the sum of the entries strictly below the diagonal, multiplied by two divided by n(n−1), as in the source's TeX, lines 176–179. Nat.cast explicitly includes the natural dimension in the real scalars. Real division is total, so the same definition gives zero in dimensions zero and one.

**Definition 1.3 (Standard deviation of the correlations).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(c: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.stdCorr}\left(c\right): \mathbb{R}\right) = \operatorname{Real.sqrt}\left(\left(\left(\frac{2}{\left(\left(\operatorname{Nat.cast}\left(n\right): \mathbb{R}\right)\right) \cdot \left(\left(\left(\operatorname{Nat.cast}\left(n\right): \mathbb{R}\right)\right) - \left(1\right)\right)}\right) \cdot \left(\sum_{\left(i: \operatorname{Fin}\left(n\right)\right)} \left(\sum_{\left(j: \operatorname{Fin}\left(n\right)\right), j < i} \left(\left(c\left(i, j\right)\right)^{2}\right)\right)\right)\right) - \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.meanCorr}\left(c\right)\right)^{2}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Estimation/CorrelationTopEigenvectorWeight.stdCorr` (`✓ std3`).

*Citation.* Yuriy Stepanov; Hendrik Herrmann; Thomas Guhr (2021). *Generic features in the spectral decomposition of correlation matrices*. DOI: [10.1063/5.0054438](https://doi.org/10.1063/5.0054438). URL: <https://arxiv.org/abs/2104.08966v1>.

*Commentary.*

The standard deviation is the real square root of the mean squared off-diagonal entry minus the square of the mean correlation, as in the source's TeX, lines 180–184. Both sums use the strict lower triangle. The definition is total for arbitrary real matrices: real square root is zero for a negative argument.

**Definition 1.4 (The normalized diagonal vector).**

$$\forall \left(n: \mathbb{N}\right), \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.delta}\left(n\right): \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)\right) = \operatorname{WithLp.toLp}\left(2, \operatorname{Function.const}\left(\operatorname{Fin}\left(n\right), \operatorname{Inv.inv}\left(\operatorname{Real.sqrt}\left(\left(\operatorname{Nat.cast}\left(n\right): \mathbb{R}\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Estimation/CorrelationTopEigenvectorWeight.delta` (`✓ std3`).

*Citation.* Yuriy Stepanov; Hendrik Herrmann; Thomas Guhr (2021). *Generic features in the spectral decomposition of correlation matrices*. DOI: [10.1063/5.0054438](https://doi.org/10.1063/5.0054438). URL: <https://arxiv.org/abs/2104.08966v1>.

*Commentary.*

The source's diagonal vector has every coordinate equal to the reciprocal square root of n (TeX, lines 154–157). Function.const forms the constant coordinate family, and WithLp.toLp places it in real Euclidean space. Its squared norm is one when n is positive; at dimension zero the vector is the unique empty vector.

**Definition 1.5 (A strict gap above each top eigenvector weight).**

$$\forall \left(n: \mathbb{N}\right), \left(\forall \left(c: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.SatisfiesWGap}\left(c\right)\right) \Leftrightarrow \left(\forall \left(v: \operatorname{OrthonormalBasis}\left(\operatorname{Fin}\left(n\right), \mathbb{R}, \operatorname{EuclideanSpace}\left(\mathbb{R}, \operatorname{Fin}\left(n\right)\right)\right)\right), \left(\forall \left(l: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{R}\right)\right), \left(\left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Matrix.mulVec}\left(c, \left(\operatorname{WithLp.ofLp}\left(\operatorname{DFunLike.coe}\left(v, j\right)\right): \left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{R}\right)\right)\right) = \operatorname{SMul.smul}\left(l\left(j\right), \left(\operatorname{WithLp.ofLp}\left(\operatorname{DFunLike.coe}\left(v, j\right)\right): \left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{R}\right)\right)\right)\right)\right) \to \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(l\left(j\right) \le l\left(i\right)\right)\right) \to \left(\exists \left(j: \operatorname{Fin}\left(n\right)\right), \left(\left(j \ne i\right) \land \left(\left(\operatorname{inner}\left(\mathbb{R}, \operatorname{DFunLike.coe}\left(v, i\right), \operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.delta}\left(n\right)\right)\right)^{2} < \left(\operatorname{inner}\left(\mathbb{R}, \operatorname{DFunLike.coe}\left(v, j\right), \operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.delta}\left(n\right)\right)\right)^{2}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Estimation/CorrelationTopEigenvectorWeight.SatisfiesWGap` (`✓ std3`).

*Citation.* Yuriy Stepanov; Hendrik Herrmann; Thomas Guhr (2021). *Generic features in the spectral decomposition of correlation matrices*. DOI: [10.1063/5.0054438](https://doi.org/10.1063/5.0054438). URL: <https://arxiv.org/abs/2104.08966v1>.

*Commentary.*

For every orthonormal eigenbasis v with eigenvalue function l, each index i whose eigenvalue is maximal has another index j with strictly larger squared projection on delta n. This is the source's basis-independent meaning of a matrix satisfying w₁ < w_max (TeX, lines 877–879), with every maximal index allowed in place of a fixed ordering. DFunLike.coe applies the basis to an index; WithLp.ofLp makes the coordinate functions in the eigenvector equation explicit. The predicate itself does not assume that the matrix is a correlation matrix.

**Definition 1.6 (The domain left between the two known regions).**

$$\forall \left(c: \mathbb{R}\right), \left(\forall \left(\sigma: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.domainD}\left(c, \sigma\right)\right) \Leftrightarrow \left(\left(\left(0 < c\right) \land \left(\left(0 < \sigma\right) \land \left(\left(\left(c\right)^{2}\right) + \left(\left(\sigma\right)^{2}\right) < 1\right)\right)\right) \land \left(\left(\neg \left(\left(\frac{1}{2} \le c\right) \lor \left(\sigma < c\right)\right)\right) \land \left(\neg \left(\left(\left(\operatorname{Real.sqrt}\left(\left(3: \mathbb{R}\right)\right)\right) \cdot \left(c\right) < \sigma\right) \lor \left(\left(c < \sigma\right) \land \left(\sigma < \left(1\right) - \left(c\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Estimation/CorrelationTopEigenvectorWeight.domainD` (`✓ std3`).

*Citation.* Yuriy Stepanov; Hendrik Herrmann; Thomas Guhr (2021). *Generic features in the spectral decomposition of correlation matrices*. DOI: [10.1063/5.0054438](https://doi.org/10.1063/5.0054438). URL: <https://arxiv.org/abs/2104.08966v1>.

*Commentary.*

The domain consists of positive c and σ inside the unit disk, outside both A₁ and A₂ from the source's TeX, lines 510–518. Thus neither c ≥ 1/2 nor σ < c holds, and neither σ > √3 c nor c < σ < 1−c holds. In particular, σ = c and the non-strict wedge boundaries are retained whenever the other defining inequalities hold.

**Definition 1.7 (The eventual-existence question).**

$$\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.claim}\right) \Leftrightarrow \left(\forall \left(c: \mathbb{R}\right), \left(\forall \left(\sigma: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.domainD}\left(c, \sigma\right)\right) \to \left(\left(\exists \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\left(m \le n\right) \to \left(\exists \left(a: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.IsCorrelation}\left(a\right)\right) \land \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.meanCorr}\left(a\right) = c\right) \land \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.stdCorr}\left(a\right) = \sigma\right) \land \left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.SatisfiesWGap}\left(a\right)\right)\right)\right)\right)\right)\right)\right)\right) \Leftrightarrow \left(c < \sigma\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Estimation/CorrelationTopEigenvectorWeight.claim` (`✓ std3`).

*Citation.* Yuriy Stepanov; Hendrik Herrmann; Thomas Guhr (2021). *Generic features in the spectral decomposition of correlation matrices*. DOI: [10.1063/5.0054438](https://doi.org/10.1063/5.0054438). URL: <https://arxiv.org/abs/2104.08966v1>.

*Commentary.*

Question III.5 asks for correlation matrices at each point of the remaining domain in sufficiently large dimensions (source TeX, lines 525–527). Here sufficiently large means that there is a natural threshold m such that every natural n ≥ m admits a matrix a with exactly mean c, standard deviation σ and the strict weight gap. The threshold may depend on c and σ, and the matrix may depend on n. The displayed proposition specifies that this existence holds exactly when c < σ.

**Theorem 1.8 (Eventual existence holds exactly above the diagonal).**

$$\forall \left(c: \mathbb{R}\right), \left(\forall \left(\sigma: \mathbb{R}\right), \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.domainD}\left(c, \sigma\right)\right) \to \left(\left(\exists \left(m: \mathbb{N}\right), \left(\forall \left(n: \mathbb{N}\right), \left(\left(m \le n\right) \to \left(\exists \left(a: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.IsCorrelation}\left(a\right)\right) \land \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.meanCorr}\left(a\right) = c\right) \land \left(\left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.stdCorr}\left(a\right) = \sigma\right) \land \left(\operatorname{D5.S3.Estimation.CorrelationTopEigenvectorWeight.SatisfiesWGap}\left(a\right)\right)\right)\right)\right)\right)\right)\right)\right) \Leftrightarrow \left(c < \sigma\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/CorrelationTopEigenvectorWeight.result` (`✓ std3`). ∎

*Resolves.* `Problems/stepanov-herrmann-guhr-2021-correlation-top-eigenvector-weight` (proved) by `D5/S3/Estimation/CorrelationTopEigenvectorWeight.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"stepanov-herrmann-guhr-2021-correlation-top-eigenvector-weight","declaration_gid":"D5/S3/Estimation/CorrelationTopEigenvectorWeight.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Yuriy Stepanov; Hendrik Herrmann; Thomas Guhr (2021). *Generic features in the spectral decomposition of correlation matrices*. DOI: [10.1063/5.0054438](https://doi.org/10.1063/5.0054438). URL: <https://arxiv.org/abs/2104.08966v1>.

*Commentary.*

First, the defining inequalities for the domain give 0 < c < 1/2 and c ≤ σ. Either σ = c, or 1−c ≤ σ ≤ √3 c; the inequality c²+σ² < 1 holds in both cases. We exclude the diagonal σ = c before constructing matrices in the second case.

In dimensions zero and one the mean is zero, and in dimension two the standard deviation is zero. These dimensions cannot have mean and standard deviation both equal to a positive c. For n ≥ 3, choose an orthonormal eigenbasis v of a correlation matrix a, write l for its eigenvalues, and set μ j = l j−1 and w j = ⟨v j, delta n⟩². The trace and squared Frobenius norm give Σ μ j = 0 and Σ (μ j)² = n(n−1)(c²+σ²). Parseval gives nonnegative weights with Σ w j = 1. Expanding the Rayleigh quotient of delta n gives Σ μ j w j = (n−1)c. If the strict weight gap holds and i has maximal eigenvalue, another weight is larger than w i, so w i < 1/2.

Choose j with the largest μ j among indices other than i. Bounding the weighted sum on those indices and using w i < 1/2 gives 2(n−1)c ≤ μ i+μ j. Apply Cauchy–Schwarz to the remaining n−2 entries, whose sum is −(μ i+μ j), and use (μ i−μ j)² ≥ 0 for the two selected entries. Together these imply n(μ i+μ j)² ≤ 2(n−2)Σ (μ k)². Substitution yields 2(n−1)c² ≤ (n−2)(c²+σ²), hence c² < σ² because c > 0. Thus a matrix with σ = c cannot satisfy the gap in any dimension. If eventual existence held while c < σ failed, the domain inequality c ≤ σ would force equality; taking n = m would contradict this obstruction.

For the converse suppose c < σ. Set L = (σ²−(1−c)²)/(σ²+(1−c)²), U = (σ²−c²)/(c²+σ²), and x = (L+min(c,U))/2. The domain inequalities give 0 ≤ L < x < min(c,U) < 1/2. Consequently a = σ/√(1−x²) and b = c−a x satisfy a > 0, b > 0, 1−a−b > 0 and 2c < a+b. The bounds x < c, x > L and x < U respectively ensure the last three strict inequalities after squaring positive quantities.

For each natural n, choose the integer k nearest to n(1+√x)/2 and put z = ((2k−n)²−n)/(n(n−1)), with n and k included in the real scalars in these expressions. The rounding error is at most one half, so k/n tends to (1+√x)/2 and z tends to x. Continuity of square root and division then shows that, for every sufficiently large n, a = σ/√(1−z²), b = c−a z and d = 1−a−b are positive. The same limit argument gives n ≥ 3, 0 < k < n, 2k ≠ n, −1 < z < 1, and 2(n−1)c < (n−2)(a+b). The integer inequalities use the natural dimension cast to the integers.

Let s have k entries equal to one and the remaining entries equal to minus one, let u be the all-ones vector, and form the matrix dI+a ssᵀ+b uuᵀ. There are n(n−1)/2 entries strictly below the diagonal. Apply the pair representation in the first projection of SignPairUStatisticMoments.sign_pair_u_statistic_moments to the corresponding integer units, taking its product-law mean parameter to be zero. The sign sum is 2k−n; swapping the triangular indices and clearing the nonzero denominator gives the lower-triangle sum of s i s j as ((2k−n)²−n)/2. Positive coefficients make the matrix positive semidefinite, and s i squared equal to one makes its diagonal equal to d+a+b = 1. The two lower-triangle identities give mean a z+b = c and second moment a²+b²+2abz. Subtracting c² leaves a²(1−z²) = σ², whose nonnegative square root is σ.

It remains to prove the strict weight gap in every eigenbasis of this matrix. For an arbitrary orthonormal eigenbasis v with eigenvalues l, put μ j = l j−d, e j = ⟨v j,u⟩ and f j = ⟨v j,s⟩. Taking inner products of the eigenvector equations gives diagonal μ = a ffᵀ+b eeᵀ. Factor this diagonal matrix through two columns: its rank is at most two, so at most two μ j are nonzero. Its diagonal identity gives μ j = a(f j)²+b(e j)² ≥ 0, and μ j = 0 forces e j = 0. Parseval gives Σ (e j)² = Σ (f j)² = n, and summing the diagonal identity gives Σ μ j = n(a+b). The sign sum gives ⟨u,s⟩ = 2k−n; applying the matrix to u therefore yields Σ μ j(e j)² = a(2k−n)²+bn². The strict inequality 2(n−1)c < (n−2)(a+b), together with c = a z+b, is exactly 2Σ μ j(e j)² < (Σ μ j)(Σ (e j)²).

Fix any maximal eigenvalue index i. The strict inequality rules out having only one nonzero μ j, so there is another nonzero index j distinct from i, and all the sums reduce to these two indices. It follows that (μ i−μ j)((e i)²−(e j)²) < 0. Maximality gives μ j ≤ μ i, hence (e i)² < (e j)². Since delta n is u multiplied by the positive reciprocal square root of n, multiplying by its square preserves this strict inequality and gives the required comparison of weights. The common threshold from the limit estimates therefore supplies the required matrix in every n ≥ m, proving the reverse implication.

## References

- Truth anchor: `D5/S3/Estimation/CorrelationTopEigenvectorWeight.IsCorrelation`
- Truth anchor: `D5/S3/Estimation/CorrelationTopEigenvectorWeight.SatisfiesWGap`
- Truth anchor: `D5/S3/Estimation/CorrelationTopEigenvectorWeight.claim`
- Truth anchor: `D5/S3/Estimation/CorrelationTopEigenvectorWeight.delta`
- Truth anchor: `D5/S3/Estimation/CorrelationTopEigenvectorWeight.domainD`
- Truth anchor: `D5/S3/Estimation/CorrelationTopEigenvectorWeight.meanCorr`
- Truth anchor: `D5/S3/Estimation/CorrelationTopEigenvectorWeight.result`
- Truth anchor: `D5/S3/Estimation/CorrelationTopEigenvectorWeight.stdCorr`
- Dependency: [D5/S3/Estimation/DecisionRisk/SignPairUStatisticMoments](DecisionRisk/SignPairUStatisticMoments.md)
