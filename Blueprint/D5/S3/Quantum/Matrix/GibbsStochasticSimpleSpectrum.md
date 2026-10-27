# A simple-spectrum Gibbs-stochastic matrix for every positive vector

## Abstract

Every strictly positive Gibbs vector admits a column-stochastic matrix with simple complex spectrum.

**Definition 1.1 (Simple complex eigenvalues).**

$$\forall (n: \mathbb{N}), (\forall (P: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), ((\operatorname{HasSimpleEigenvalues}\left(P\right)) \Leftrightarrow (\operatorname{Multiset.Nodup}\left(\operatorname{Polynomial.roots}\left(\operatorname{Matrix.charpoly}\left(\operatorname{Matrix.map}\left(P, \operatorname{DFunLike.coe}\left(\operatorname{algebraMap}\left(\mathbb{R}, \mathbb{C}\right)\right)\right)\right)\right)\right))))$$

*Formalization.* `D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.HasSimpleEigenvalues` (`✓ std3`).

*Citation.* Frederik vom Ende (2024). *Almost All Quantum Channels Are Diagonalizable*. DOI: [10.1142/S1230161224500124](https://doi.org/10.1142/S1230161224500124). URL: <https://arxiv.org/abs/2403.19643v3>.

*Commentary.*

A real matrix P has only simple eigenvalues when the multiset of roots of its complex characteristic polynomial has no repeated element. The entrywise map algebraMap from the real numbers to the complex numbers, including its coercion to a function by DFunLike.coe, is displayed explicitly. The source defines a simple eigenvalue as one of algebraic multiplicity one in channel_diag_approx.tex, lines 123-125. Since the complex characteristic polynomial splits, this predicate says that all n roots are distinct; for n = 0 the polynomial is one and its root multiset is empty.

**Definition 1.2 (Existence for every positive Gibbs vector).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < d\left(i\right))) \Rightarrow (\exists (P: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), ((P \in \operatorname{thermalProcesses}\left(d\right)) \land (\operatorname{HasSimpleEigenvalues}\left(P\right)))))))$$

*Formalization.* `D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2024). *Almost All Quantum Channels Are Diagonalizable*. DOI: [10.1142/S1230161224500124](https://doi.org/10.1142/S1230161224500124). URL: <https://arxiv.org/abs/2403.19643v3>.

*Commentary.*

For every natural dimension n and every strictly positive real vector d, there is a real matrix P in thermalProcesses d with only simple complex eigenvalues. Here thermalProcesses is the set of column-stochastic matrices preserving d: each entry is nonnegative, each column sums to one, and Pd = d. The vector d need not be normalized, and zero dimension is included. This is the existence statement associated with the construction question in the source's Outlook, channel_diag_approx.tex, lines 509-513. The density consequence described by the source's Lemma lemma_hartfiel, lines 170-181, is a separate statement.

**Theorem 1.3 (A reversible chain with simple spectrum).**

$$\forall (n: \mathbb{N}), (\forall (d: (\operatorname{Fin}\left(n\right)) \to (\mathbb{R})), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) < d\left(i\right))) \Rightarrow (\exists (P: \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{R}\right)), ((P \in \operatorname{thermalProcesses}\left(d\right)) \land (\operatorname{HasSimpleEigenvalues}\left(P\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.result` (`✓ std3`). ∎

*Resolves.* `Problems/vom-ende-2024-gibbs-stochastic-simple-spectrum` (proved) by `D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"vom-ende-2024-gibbs-stochastic-simple-spectrum","declaration_gid":"D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Frederik vom Ende (2024). *Almost All Quantum Channels Are Diagonalizable*. DOI: [10.1142/S1230161224500124](https://doi.org/10.1142/S1230161224500124). URL: <https://arxiv.org/abs/2403.19643v3>.

*Commentary.*

In dimension n = m + 1, let c = sum over j of d j and put g i = d i / c. Strict positivity gives c > 0 and g i > 0, and the sum of the coordinates of g is one. Indices i and j are adjacent when i.val + 1 = j.val or j.val + 1 = i.val. For distinct adjacent indices set P i j = g i / 2, and set every other off-diagonal entry to zero. Set P j j equal to one minus the sum of g k / 2 over indices k adjacent to j.

There are no indices adjacent to themselves. In column j, the off-diagonal sum is exactly the sum subtracted from P j j, so each column sums to one. For a nonnegative vector g whose coordinates sum to at most one, that subtracted sum is at most half the total sum. Thus each diagonal entry is at least one half, and every off-diagonal entry is nonnegative.

The entry formula gives detailed balance, (P i j)(g j) = (P j i)(g i), also at diagonal and nonadjacent positions. Summing over j and using the column sum at i proves Pg = g. Since d = c times g and matrix-vector multiplication commutes with scalar multiplication, Pd = d. For the normalized vector above, these facts give P in thermalProcesses d.

Let D be diagonal with entry sqrt(g i), and let E be diagonal with entry (sqrt(g i)) inverse. Positivity gives DE = I. Put S = EPD. The identity Matrix.charpoly_mul_comm applied to (EP)D gives charpoly(S) = charpoly(D(EP)) = charpoly(P), using associativity and DE = I.

To express S as a Jacobi matrix, let a i = P i i and define e i = sqrt(g i) times sqrt(g(next i)) divided by two, where next i has value min(i.val + 1, m). Each e at an index t.castSucc with t in Fin m is positive. Checking diagonal, upper-adjacent, lower-adjacent and nonadjacent entries gives S = jacobiMatrix m a e. The adjacent entries are sqrt(g i) times sqrt(g j) divided by two; the cancellation uses g i / sqrt(g i) = sqrt(g i).

For a Jacobi matrix J = jacobiMatrix m a e with these nonzero adjacent coefficients, suppose Jv = mu times v and v at Fin.last m is zero. The symmetric outer product X = vv transpose satisfies JX = X diag(mu), where diag(mu) is the constant diagonal matrix. Compare X with the zero matrix using the endpoint-uniqueness theorem symmetric_jacobi_intertwiner_unique of ZeitlinSixJ.Inverse: both are symmetric intertwiners and their last diagonal entries agree. Hence X = 0, which implies v = 0.

The real symmetric matrix J is Hermitian, so choose its orthonormal eigenvector basis. Every basis vector has a nonzero last coordinate by the preceding implication. If the eigenvalues at i and j agree, put x and y equal to their basis vectors, c equal to the last coordinate of y, and b equal to the last coordinate of x. Then c times x minus b times y is an eigenvector with zero last coordinate, and therefore vanishes. If i and j were distinct, its ith basis coefficient would give c = 0, contradicting the nonzero last coordinate of y. Thus the eigenvalue function on the basis indices is injective.

The Hermitian characteristic polynomial splits over the real numbers, and its root multiset is the image of the basis indices under that eigenvalue function. Injectivity makes this multiset have no repetitions. The injective map algebraMap from the real numbers to the complex numbers preserves this property, and Matrix.charpoly_map identifies the resulting multiset with the roots of the complex characteristic polynomial of J.

In dimension zero, take the identity matrix. It is column stochastic and fixes the empty vector; its characteristic polynomial is one, with no roots. Finally split n into zero or m + 1. In the positive-dimensional case choose the matrix P constructed from the normalized vector g. Its column stochasticity and preservation of d give membership in thermalProcesses d. Apply Matrix.charpoly_map, the equality of the characteristic polynomials of P and S, and S = jacobiMatrix m a e. The simple complex spectrum of J then proves HasSimpleEigenvalues P.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.HasSimpleEigenvalues`
- Truth anchor: `D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.claim`
- Truth anchor: `D5/S3/Quantum/Matrix/GibbsStochasticSimpleSpectrum.result`
- Dependency: [D5/S3/Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer](../../Combinatorics/Graph/LegalWords/ConstrainedHarmonicOptimizer.md)
- Dependency: [D5/S3/Quantum/Algebra/ZeitlinSixJ/Inverse](../Algebra/ZeitlinSixJ/Inverse.md)
- Dependency: [D5/S3/StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation](../../StatisticalMechanics/ThermalProcessSelfDualFactorizationRefutation.md)
