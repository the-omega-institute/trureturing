---
slug: hiai-2026-spectral-geometric-log-euclidean-refutation
bibkey: hiai2025logmajorizationle
doi: 10.1016/j.laa.2026.01.003
url: https://arxiv.org/abs/2510.04691v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.result
---

# Hiai's spectral geometric Log-Euclidean comparison fails

## Problem

Fumio Hiai, *Log-majorizations between quasi-geometric type means for matrices*,
Linear Algebra Appl. 735 (2026), 123–174; arXiv:2510.04691v3.

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

## Motivation

The small-power limit of the spectral geometric mean is the Log-Euclidean mean.
An upper log-majorization bound would connect the finite-power comparison to that limit.

## Gap

The open case quantifies over every α > 1, p > 0 and positive definite matrix pair.
A two-dimensional pair violating the singleton eigenvalue inequality refutes it.
Preregistration: issue #16129.

## Route

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

## Falsifier

The largest eigenvalue of $SG_{2,1}(A,B)$ exceeds 2, whereas every eigenvalue
of $LE_2(A,B)$ is at most 2. The asserted product inequality already fails for one
eigenvalue, irrespective of the determinant equality clause.

## Evidence

`D5/S3/Quantum/Matrix/SpectralGeometricLogEuclideanRefutation.lean` fixes `mpow`, `wgm`, `specMean`, `SG`, `LE`,
`LogMajorized`, and `claim`, and exposes `result : ¬ claim`. All witness data and
proof helpers are private. The proof uses the continuous functional calculus,
positive definite inputs, the genuine inverse of A, the positive square-root
certificate and spectral bounds. Parameter-family reasoning below is not separately formalized.

## Triage

### What the settlement shows

1. **Proved (Lean) — the open case fails.** The α = 2, p = 1 pair above satisfies
   both positive definiteness hypotheses and refutes the open case of Problem 3.20.

2. **Reasoning (exact mathematics, not separately formalized) — every p > 0 at α = 2.**
   For positive definite matrices and r > 0, $X\prec_{\log}Y$ if and only if
   $X^r\prec_{\log}Y^r$: ordered eigenvalue products and determinant equality
   are both preserved and reflected by the positive scalar power. For any p > 0,
   take $(A^{1/p},B^{1/p})$. Then
   $SG_{2,p}(A^{1/p},B^{1/p})=SG_{2,1}(A,B)^{1/p}$ and
   $LE_2(A^{1/p},B^{1/p})=LE_2(A,B)^{1/p}$, so the comparison fails.

3. **Reasoning (exact mathematics, not separately formalized) — every α > 1.**
   Fix α > 1, let b = $e^{2\alpha}$, x = 1/b, and put

   $$
   A_t=\operatorname{diag}(1,t^2),\qquad
   U_x=\begin{pmatrix}\sqrt{1-x}&\sqrt x\\-\sqrt x&\sqrt{1-x}\end{pmatrix},\qquad
   B=U_x\operatorname{diag}(1,b)U_x^{\mathsf T}.
   $$

   Write u = 2 − 1/b, w = b − 1 + 1/b, and $v=(b-1)\sqrt{x(1-x)}$,
   so $B=\begin{pmatrix}u&v\\v&w\end{pmatrix}$ and $\det B=b$.
   With $L_t=A_t^{-1}\#B$, the two-dimensional square-root formula gives

   $$
   L_t=\frac1{\sqrt{u+t^2w+2t\sqrt b}}
   \begin{pmatrix}u+t\sqrt b&v\\v&w+\sqrt b/t\end{pmatrix}
   \longrightarrow\operatorname{diag}(\sqrt{b/w},0)
   \quad(t\to\infty).
   $$
   The exact identity $F_\alpha=L_t^{\alpha-1}B L_t^{\alpha-1}$ follows from
   $L_tA_tL_t=B$. Since α − 1 > 0, continuity of positive powers at zero gives

   $$
   \lambda_{\max}(F_\alpha(A_t,B))\longrightarrow
   u(b/w)^{\alpha-1}>13/7.
   $$

   Indeed b > $e^2$ > 7, so u > 13/7 and b/w > 1. The upper-left entry of
   $(1-\alpha)\log A_t+\alpha\log B$ is $\alpha x\log b$; its lower-right entry
   tends to −∞ and its off-diagonal entry stays fixed. Hence

   $$
   \lambda_{\max}(LE_\alpha(A_t,B))\longrightarrow
   \exp(2\alpha^2e^{-2\alpha})<7/5.
   $$

   The exponent has derivative $4\alpha(1-\alpha)e^{-2\alpha}<0$ for α > 1
   and is below $2/e^2<2/7$. The exponential series gives
   $\exp(2/7)<\sum_{k\ge0}(2/7)^k=7/5$; its inequality is strict for k ≥ 2. The separated limits give finite t with a strict singleton
   violation. The positive-power reduction extends this to every p > 0.
   Thus the α > 1 cell of the table is “none”.

4. **Consequences (logical reasoning, not separately formalized) — the sufficient route fails.**
   Using the paper's limit $LE_\alpha=\lim_{q\downarrow0}SG_{\alpha,q}$, a comparison
   $SG_{\alpha,p}\prec_{\log}SG_{\alpha,q}$ for all α > 1 and p ≥ q > 0 would,
   by continuity of eigenvalues and determinants as q decreases to zero, imply
   $SG_{\alpha,p}\prec_{\log}LE_\alpha$. The refutation excludes that universal route
   in Problem 3.20's note. This consequence uses the stated limit from the paper.

5. **Open — companion questions.** The companion questions of Problem 3.12 for
   α > 1 beyond this consequence remain unresolved here.

## ASSUMED-UNVERIFIED

The positive-power reduction, all-α asymptotic family, and consequence using the
paper's small-power limit are exact mathematical reasoning, not additional Lean
conclusions. The remaining companion questions of Problem 3.12 are open here.
