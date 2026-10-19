---
bibkey: bhatia1997matrixanalysis
authors: Rajendra Bhatia
year: 1997
title: Matrix Analysis
doi: 10.1007/978-1-4612-0653-8
url: https://doi.org/10.1007/978-1-4612-0653-8
claim: "Singular-value inequalities, Courant–Fischer comparison, symmetric gauge representations of unitarily invariant norms, and Fan dominance supply the matrix-analysis background."
strata_touched:
  - D5/S3/Quantum/Schatten/UnitarilyInvariantNorm
  - D5/S3/Quantum/Schatten/SingularValueOrder
  - D5/S3/Quantum/Schatten/DiagonalSingularValues
  - D5/S3/Quantum/Schatten/LowerGelfandNaimark
  - D5/S3/Quantum/Schatten/ExpandingGram
  - D5/S3/Quantum/Schatten/UINormContinuity
  - D5/S3/Quantum/Schatten/RankOneHadamard
license: citation-only
triage: anchor
---

# Matrix Analysis

Rajendra Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics **169**,
Springer, 1997, Chapters III–IV.

## Mathematical background

The singular values $s_1(X)\ge\cdots\ge s_n(X)\ge0$ are the square roots
of the decreasing eigenvalues of $X^*X$. Courant–Fischer implies that
$A^*A\preceq B^*B$ gives $s_i(A)\le s_i(B)$. Singular values are unchanged
by unitary multiplication and adjunction and scale by the absolute value
of a scalar. For a nonnegative diagonal matrix they are its entries in
decreasing order. Rank at most one is equivalent to an outer-product
factorization, allowing the zero matrix.

Every unitarily invariant norm has the symmetric gauge representation
$N(X)=\gamma(s(X))$, with $\gamma(x)=N(\operatorname{diag}(x))$.
The gauge is invariant under permutations and sign changes, is monotone
under coordinatewise absolute-value domination, and is monotone under
weak majorization of nonnegative decreasing vectors. The last implication
is the Fan dominance direction. Transposition and adjunction preserve
$N$. Like every norm on a finite-dimensional space, $N$ is continuous.

The lower Gelfand–Naimark inequality gives, for invertible complex square
matrices $C,D$ and every subset $I\subseteq\{1,\ldots,n\}$,

$$
\prod_{i\in I}\frac{s_i(CD)}{s_i(D)}
\le \prod_{j=1}^{|I|}s_j(C).
$$

If $T^*T\succeq I$, then $T$ is invertible, $TT^*\succeq I$, and
$s_i(AT)\ge s_i(A)$ for every square $A$. These are classical spectral
comparisons. The rank-one Hadamard reduction, expanding diagonal
minimization, and balanced product argument use these comparisons to
obtain the variational conclusion; that conclusion is not attributed to
this book.

## Locator

DOI: 10.1007/978-1-4612-0653-8

Source: https://doi.org/10.1007/978-1-4612-0653-8

The bibliographic scope is Chapters III–IV. No finer
theorem numbering or direct page inspection is asserted. The background
attribution does not assert that the book states the Lean signatures,
the unsorted comparison-vector variant of the gauge inequality, or the
empty-dimensional extensions verbatim. No online source verification or
exhaustive literature check is included.
