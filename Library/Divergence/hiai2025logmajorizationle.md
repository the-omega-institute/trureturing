---
bibkey: hiai2025logmajorizationle
authors: Fumio Hiai
year: 2026
title: "Log-majorizations between quasi-geometric type means for matrices"
doi: null
url: https://arxiv.org/abs/2510.04691v3
claim: "Problem 3.20. The case remaining open is whether SGα,p ≺log LEα for α > 1. Note that this is affirmative if SGα,p ≺log SGα,q if α > 1 and p ≥ q (see Problem 3.12)."
strata_touched:
  - D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation
license: citation-only
triage: anchor
---

## Locator

Canonical publication metadata: [original geometric trace and support extension](hiai2025geometrictraceconvexity.md).

Author text: <https://arxiv.org/abs/2510.04691v3>.
- DOI: https://doi.org/10.1016/j.laa.2026.01.003

Fumio Hiai, *Log-majorizations between quasi-geometric type means for matrices*,
Linear Algebra Appl. 735 (2026), 123–174; arXiv:2510.04691v3, §2 and Problem 3.20.

## Spectral geometric and Log-Euclidean means

§2, equation (2.3), verbatim:

> Fα(A, B) := (A^{−1}#B)^α A(A^{−1}#B)^α.

§2, equation (2.4), verbatim:

> SGα,p(A, B) := Fα(A^p, B^p)^{1/p}.

§2, Log-Euclidean and weighted geometric mean definitions, verbatim:

> LEα(A, B) := exp((1 − α) log A + α log B)

> A#αB := A^{1/2}(A^{−1/2}BA^{−1/2})^α A^{1/2}

Here # = #_{1/2}.

Problem 3.20, verbatim:

> Problem 3.20. The case remaining open is whether SGα,p ≺log LEα for α > 1. Note that this is affirmative if SGα,p ≺log SGα,q if α > 1 and p ≥ q (see Problem 3.12).

The summary table after Problem 3.20 has row “SGα,p ≺log LEα”, with entries
“none” for 0 < α < 1 and “?” for α > 1.

## Repository-derived result

Take $m=2$, $\alpha=2$, $p=1$, and

$$
A=\operatorname{diag}(1,2^{20}),\qquad
B=\frac1{125}\begin{pmatrix}272&504\\504&1853\end{pmatrix}
 =U\operatorname{diag}(1,16)U^{\mathsf T},\qquad
U=\frac1{25}\begin{pmatrix}24&7\\-7&24\end{pmatrix}.
$$

Both matrices are positive definite. Put $T=77761424/5$ and
$H=B+4096A^{-1}$. For $X=A^{1/2}BA^{1/2}$,

$$
\det X=2^{24},\qquad
(X+4096I)^2=T X,\qquad
X^{1/2}=\frac{X+4096I}{\sqrt T}.
$$

Positivity identifies the square root uniquely. Thus
$L=A^{-1}\#B=H/\sqrt T$ and $LAL=B$. Consequently,

$$
SG_{2,1}(A,B)=L^2AL^2=LBL=\frac{HBH}{T},\qquad
SG_{2,1}(A,B)_{00}=\frac{286558676}{121502225}>2.
$$

On the Log-Euclidean side,

$$
-\log A+2\log B=(\log2)N,\qquad
N=\frac1{625}\begin{pmatrix}392&1344\\1344&-7892\end{pmatrix}.
$$

The factorization

$$
I-N=
\begin{pmatrix}1&0\\-1344/233&1\end{pmatrix}
\operatorname{diag}(233/625,285/233)
\begin{pmatrix}1&-1344/233\\0&1\end{pmatrix}
$$

proves $N\le I$. Therefore every eigenvalue of $LE_2(A,B)$ is at most
$\exp(\log2)=2$. A Hermitian matrix whose eigenvalues are all at most 2 is
bounded above by $2I$, so the displayed diagonal entry forces an eigenvalue
of $SG_{2,1}(A,B)$ greater than 2. The singleton case of log-majorization fails;
no determinant computation is needed.

The Lean theorem `result : ¬ claim` proves the finite-dimensional refutation
with the CFC definitions of both means.

## Neighboring references

Problem 3.12 concerns comparisons between spectral geometric means at different
power parameters. Problem 3.20 identifies their decreasing-parameter comparison
as a sufficient route to the Log-Euclidean bound. The companion problem separates
the exact Lean instance, parameter-family reasoning, and the remaining questions.

## ASSUMED-UNVERIFIED

The all-parameter analysis and the consequence for Problem 3.12 in the companion
problem are mathematical reasoning rather than additional Lean theorems.
