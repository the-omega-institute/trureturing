---
bibkey: petrturek2025wreath
authors: Jan Petr; Pavel Turek
year: 2025
title: The wreath matrix
doi: 10.48550/arXiv.2501.07269
url: https://arxiv.org/abs/2501.07269v2
claim: "Question 5.5 asks whether the eigenvalues λ₁, λ₂, …, λₖ from Theorem 1.5 are all distinct."
strata_touched:
  - D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: 10.48550/arXiv.2501.07269

Source: https://arxiv.org/abs/2501.07269v2

The page numbers refer to arXiv version 2.

## Theorem 1.5

Page 3 states: “Let $k<\frac n2$ be two positive integers and let
$g=\gcd(n,k)$. The $(n,k)$-wreath matrix has $k+1$ eigenvalues”

$$\lambda_1\geq\lambda_2,\lambda_3,\ldots,\lambda_k>\lambda_0=0,$$

“all of which are integers.” The same theorem states: “The value of
$\lambda_1$ is $\frac{n(n-k)!k!}{2g(g!)^{n/g}}$ if $k\nmid n$ and
$\frac{n^2(n-k)!}{k^2(k!)^{n/k-1}(\frac nk)!}$ if $k\mid n$.”

It continues: “If $g=1$, for $2\leq l\leq k$ we moreover have”

$$
\lambda_l=(-1)^l\frac12 l!k!(n-k-l)!(n-2k-1)\binom{k}{l}
-\frac12 k!(n-k)!
+l!\binom{k+1}{l+1}\sum_{j=0}^l(-1)^{l-j}(k-j)!(n-k-l+j)!.
$$

The paragraph after the theorem states: “We stress that the theorem does not
say that the $k+1$ eigenvalues are pairwise distinct (see Question 5.5).”
When values coincide, that paragraph adds their listed multiplicities.

## Question 5.5

Page 16 asks verbatim:

> Are the eigenvalues $\lambda_1,\lambda_2,\ldots,\lambda_k$ from Theorem 1.5 all distinct?

The Lean `lambdaOne` and `lam` are these formulas with rational values.
Natural-number subtraction is truncated; `Nat.div` is natural-number
division. In the positive coprime range $2k<n$, the factorial arguments and
the finite sum agree with the source. The separate factor $n-2k-1$ is
evaluated in the rationals. `claim` restricts the affirmative answer to
coprime parameters, so its negation suffices to answer the question
negatively. The Lean arithmetic refutation uses $n=14$, $k=5$ and indices
$3,5$, whose formula values both equal $17107200$.

The identification of these formulas with the matrix spectrum is supplied
by the published theorem and is not formalized in the settling module.
The source's wreath conjecture is outside this refutation's scope.
