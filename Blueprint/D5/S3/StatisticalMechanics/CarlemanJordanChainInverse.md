# Critical Carleman matrices and normalized Jordan chains

## Abstract

The inverse of each normalized critical Carleman Jordan chain is an increasing-path sum.

**Definition 1.1 (A principal Carleman truncation).**

$$\forall \left(\alpha: \left(\mathbb{N}\right) \to \left(\mathbb{R}\right)\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.carleman}\left(\alpha, n, i, j\right) = \operatorname{PowerSeries.coeff}\left(\left(\operatorname{Fin.val}\left(j\right)\right) + \left(1\right), \left(\operatorname{PowerSeries.mk}\left(\alpha\right)\right)^{\left(\operatorname{Fin.val}\left(i\right)\right) + \left(1\right)}\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.carleman` (`✓ std3`).

*Citation.* Nicolas Grosjean; Thierry Huillet (2016). *Some combinatorial aspects of discrete non-linear population dynamics*. DOI: [10.1016/j.chaos.2016.10.004](https://doi.org/10.1016/j.chaos.2016.10.004). URL: <https://arxiv.org/abs/1610.05919v1>.

*Commentary.*

The coefficient sequence α determines the formal power series φ = PowerSeries.mk α. The entry in row i and column j is the coefficient of degree j.val + 1 in φ raised to i.val + 1. Thus Fin n indexes the first n positive powers and positive coefficient degrees, with an index shift of one. This is the principal truncation of the Carleman matrix in equation (2) of Grosjean and Huillet (snlmatrixRR.tex, lines 126–141). The definition accepts any real coefficient sequence; the critical-case assumptions enter the inverse theorem.

**Definition 1.2 (A normalized upper triangular Jordan chain).**

$$\forall \left(\alpha: \left(\mathbb{N}\right) \to \left(\mathbb{R}\right)\right), \left(\forall \left(n: \mathbb{N}\right), \left(\forall \left(w: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.IsJordanChain}\left(\alpha, n, w\right)\right) \Leftrightarrow \left(\left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{Matrix.mulVec}\left(\left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.carleman}\left(\alpha, n\right)\right) - \left(\left(1: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right)\right), \lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(w\left(i, j\right)\right)\right) = \operatorname{ite}\left(\operatorname{Fin.val}\left(j\right) = 0, \left(0: \left(\operatorname{Fin}\left(n\right)\right) \to \left(\mathbb{R}\right)\right), \lambda \left(i: \operatorname{Fin}\left(n\right)\right) \mapsto \left(w\left(i, \left(\langle\left(\operatorname{Fin.val}\left(j\right)\right) - \left(1\right)\rangle: \operatorname{Fin}\left(n\right)\right)\right)\right)\right)\right)\right) \land \left(\left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\left(\operatorname{Fin.val}\left(i\right) = 0\right) \to \left(w\left(i, j\right) = \operatorname{ite}\left(\operatorname{Fin.val}\left(j\right) = 0, \left(1: \mathbb{R}\right), \left(0: \mathbb{R}\right)\right)\right)\right)\right)\right) \land \left(\forall \left(i: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\left(j < i\right) \to \left(w\left(i, j\right) = \left(0: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.IsJordanChain` (`✓ std3`).

*Citation.* Nicolas Grosjean; Thierry Huillet (2016). *Some combinatorial aspects of discrete non-linear population dynamics*. DOI: [10.1016/j.chaos.2016.10.004](https://doi.org/10.1016/j.chaos.2016.10.004). URL: <https://arxiv.org/abs/1610.05919v1>.

*Commentary.*

Subtract the identity matrix from the Carleman truncation. A column of w whose index value is zero is annihilated by this difference, and every later column maps to the preceding column. The row at index zero has entry one in column zero and zero elsewhere, and entries below the diagonal vanish. For n > 0 these conditions make column zero the zeroth coordinate vector; for n = 0 all three conditions are vacuous. They express the normalization in the critical-case Jordanization (snlmatrixRR.tex, lines 403–428 and 439–440). In the nonzero branch, ⟨j.val − 1⟩ denotes the element of Fin n with natural value j.val − 1; the branch condition and j.val < n give its bound.

**Definition 1.3 (The increasing-path weights).**

$$\forall \left(\alpha: \left(\mathbb{N}\right) \to \left(\mathbb{R}\right)\right), \left(\forall \left(n: \mathbb{N}\right), \left(\left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.sigma}\left(\alpha, n, 0, j\right) = \operatorname{ite}\left(\operatorname{Fin.val}\left(j\right) = 0, \left(1: \mathbb{R}\right), \left(0: \mathbb{R}\right)\right)\right)\right) \land \left(\forall \left(m: \mathbb{N}\right), \left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.sigma}\left(\alpha, n, \left(m\right) + \left(1\right), j\right) = \sum_{i: \operatorname{Fin}\left(n\right)} \left(\operatorname{ite}\left(i < j, \left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.sigma}\left(\alpha, n, m, i\right)\right) \cdot \left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.carleman}\left(\alpha, n, i, j\right)\right), \left(0: \mathbb{R}\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.sigma` (`✓ std3`).

*Citation.* Nicolas Grosjean; Thierry Huillet (2016). *Some combinatorial aspects of discrete non-linear population dynamics*. DOI: [10.1016/j.chaos.2016.10.004](https://doi.org/10.1016/j.chaos.2016.10.004). URL: <https://arxiv.org/abs/1610.05919v1>.

*Commentary.*

For zero edges the weight is one at index zero and zero elsewhere. To obtain the weight of paths with m + 1 edges ending at j, sum over i < j the weight of an m-edge path ending at i multiplied by the Carleman entry from i to j. Every path is strictly increasing and starts at zero. Appending its final edge gives exactly the source's path sum, with sigma α n m j corresponding to σ(m,j.val + 1) (snlmatrixRR.tex, lines 442–449). This recurrence also covers an empty index type.

**Definition 1.4 (Existence and the critical-case inverse formula).**

$$\left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.claim}\right) \Leftrightarrow \left(\forall \left(\alpha: \left(\mathbb{N}\right) \to \left(\mathbb{R}\right)\right), \left(\left(\alpha\left(0\right) = \left(0: \mathbb{R}\right)\right) \to \left(\left(\alpha\left(1\right) = \left(1: \mathbb{R}\right)\right) \to \left(\left(\alpha\left(2\right) \ne \left(0: \mathbb{R}\right)\right) \to \left(\forall \left(n: \mathbb{N}\right), \left(\left(0 < n\right) \to \left(\left(\exists \left(w: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.IsJordanChain}\left(\alpha, n, w\right)\right)\right) \land \left(\forall \left(w: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.IsJordanChain}\left(\alpha, n, w\right)\right) \to \left(\left(\operatorname{IsUnit}\left(\operatorname{Matrix.det}\left(w\right)\right)\right) \land \left(\forall \left(k: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\left(k \le j\right) \to \left(\operatorname{Inv.inv}\left(w\right)\left(k, j\right) = \operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.sigma}\left(\alpha, n, \operatorname{Fin.val}\left(k\right), j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Nicolas Grosjean; Thierry Huillet (2016). *Some combinatorial aspects of discrete non-linear population dynamics*. DOI: [10.1016/j.chaos.2016.10.004](https://doi.org/10.1016/j.chaos.2016.10.004). URL: <https://arxiv.org/abs/1610.05919v1>.

*Commentary.*

For every real coefficient sequence with α 0 = 0, α 1 = 1 and α 2 nonzero, each positive-size principal truncation has a normalized upper triangular Jordan chain. Every matrix w satisfying those conditions has nonzero determinant, and its inverse at k ≤ j equals sigma α n k.val j. The source's conjecture W⁻¹(k,k′) = σ(k − 1,k′), for k′ ≥ k ≥ 1, becomes this identity after shifting both matrix indices by one (snlmatrixRR.tex, lines 449–452). The statement concerns finite principal truncations and formal coefficients, for which analytic convergence is unnecessary.

**Theorem 1.5 (Jordan-chain inversion by powers and paths).**

$$\forall \left(\alpha: \left(\mathbb{N}\right) \to \left(\mathbb{R}\right)\right), \left(\left(\alpha\left(0\right) = \left(0: \mathbb{R}\right)\right) \to \left(\left(\alpha\left(1\right) = \left(1: \mathbb{R}\right)\right) \to \left(\left(\alpha\left(2\right) \ne \left(0: \mathbb{R}\right)\right) \to \left(\forall \left(n: \mathbb{N}\right), \left(\left(0 < n\right) \to \left(\left(\exists \left(w: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.IsJordanChain}\left(\alpha, n, w\right)\right)\right) \land \left(\forall \left(w: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)\right), \left(\left(\operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.IsJordanChain}\left(\alpha, n, w\right)\right) \to \left(\left(\operatorname{IsUnit}\left(\operatorname{Matrix.det}\left(w\right)\right)\right) \land \left(\forall \left(k: \operatorname{Fin}\left(n\right)\right), \left(\forall \left(j: \operatorname{Fin}\left(n\right)\right), \left(\left(k \le j\right) \to \left(\operatorname{Inv.inv}\left(w\right)\left(k, j\right) = \operatorname{D5.S3.StatisticalMechanics.CarlemanJordanChainInverse.sigma}\left(\alpha, n, \operatorname{Fin.val}\left(k\right), j\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.result` (`✓ std3`). ∎

*Resolves.* `Problems/grosjean-huillet-2016-carleman-jordan-chain-inverse` (proved) by `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"grosjean-huillet-2016-carleman-jordan-chain-inverse","declaration_gid":"D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Nicolas Grosjean; Thierry Huillet (2016). *Some combinatorial aspects of discrete non-linear population dynamics*. DOI: [10.1016/j.chaos.2016.10.004](https://doi.org/10.1016/j.chaos.2016.10.004). URL: <https://arxiv.org/abs/1610.05919v1>.

*Commentary.*

Fix α with α 0 = 0, α 1 = 1 and α 2 ≠ 0, and fix n > 0. Write P = carleman α n and A = P − I. Put f = PowerSeries.mk (fun k => α (k + 1)); then φ = Xf and the constant coefficient of f is one. Extracting coefficients of X raised to i.val + 1 times f raised to i.val + 1 shows that A(i,j) = 0 for j ≤ i. When j.val = i.val + 1, the coefficient of degree one in that power of f gives A(i,j) = (↑(i.val + 1) : ℝ) α 2. This entry is nonzero, because i.val + 1 is a positive natural number and α 2 ≠ 0.

The columns are constructed by a finite substitution argument. For k < n and a vector b vanishing at every index with value at least k, construct v with Av = b, with v zero at index zero and above index k. At k = 0 take v = 0. In the step from k to k + 1, let r and p have values k and k + 1, put c = b(r)/A(r,p), and let e be supported only at p with value c. The vector b − Ae vanishes at every index with value at least k: the row r cancels by the choice of c, and the later rows vanish by the support of b and strict upper triangularity of A. The induction hypothesis gives u with Au = b − Ae, and v = u + e has the required support and image.

Now construct the columns in order. The zeroth column is the zeroth coordinate vector, which A annihilates. For a later column with index value t, the preceding column vanishes at index values at least t. Apply the substitution argument with k = t to obtain a new column with zero first coordinate, support through t and image equal to the preceding column. Replace only column t, preserving the earlier columns. After n steps the resulting matrix satisfies IsJordanChain α n w.

For any such w, induction on m gives A raised to m times column j equal to column j.val − m when m ≤ j.val, and equal to zero otherwise. The initial case uses the identity matrix; the induction step applies the chain equation, with the zeroth column terminating the chain. Define q(k,j) = (A raised to k.val)(0,j), using the zeroth finite index, which exists because n > 0. The entry (q w)(k,j) is the zeroth coordinate of A raised to k.val times column j. The first-row normalization makes this entry one exactly when k = j and zero otherwise. Hence q w = I. For finite square matrices this left inverse gives a nonzero determinant and w⁻¹ = q.

Finally, induction on m identifies (A raised to m)(0,j) with sigma α n m j. For m = 0 the first row of the identity matrix is the zero-edge path weight. For m + 1, matrix multiplication sums (A raised to m)(0,i) A(i,j) over i. If i < j, the off-diagonal entry A(i,j) equals P(i,j), and the induction hypothesis gives the shorter-path weight. If i ≥ j, strict upper triangularity makes the summand zero. The resulting sum is precisely the recurrence defining sigma. Substitution into w⁻¹ = q proves the claimed inverse entries for k ≤ j.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.IsJordanChain`
- Truth anchor: `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.carleman`
- Truth anchor: `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.result`
- Truth anchor: `D5/S3/StatisticalMechanics/CarlemanJordanChainInverse.sigma`
