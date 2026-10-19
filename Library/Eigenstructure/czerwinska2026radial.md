---
bibkey: czerwinska2026radial
authors: M. M. Czerwińska; J. A. Franco; A. Merino
year: 2026
title: "Towards a Characterization of Matrix Monotonicity via Radial Convexity"
doi: 10.48550/arXiv.2610.17393
url: https://arxiv.org/abs/2610.17393
claim: "Let f : (0, ∞) → R. Then f is radially convex of order n (with respect to the Frobenius norm) if and only if f is matrix monotone of degree n."
strata_touched:
  - D5/S3/Quantum/Matrix/RadialConvexity
  - D5/S3/Quantum/Matrix/CzerwinskaFrancoMerinoCounterexample
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/2610.17393>.

DOI: <https://doi.org/10.48550/arXiv.2610.17393>.

M. M. Czerwińska, J. A. Franco and A. Merino, *Towards a Characterization of Matrix Monotonicity via Radial Convexity*, arXiv:2610.17393v1, Definitions 1.1 and 2.15, §2 functional calculus, and §4, Conjecture 4.10.

## Conjecture and definitions

Conjecture 4.10 reads:

> Let f : (0, ∞) → R. Then f is radially convex of order n (with respect to the Frobenius norm) if and only if f is matrix monotone of degree n.

arXiv:2610.17393v1, §4, directly after Conjecture 4.10, verbatim:

> By Proposition 3.9, matrix monotonicity of degree n implies radial convexity of order n. Thus, it remains to prove the converse implication. The next theorem establishes the conjecture for n = 2.

arXiv:2610.17393v1, §1, verbatim:

> In degree 3, we show that radial convexity already provides the principal minor conditions required for matrix monotonicity, leaving the sign of the determinant of the Loewner matrix as the remaining obstruction.

For positive definite complex Hermitian matrices, $A\preceq B$ means that $B-A$ is positive semidefinite. Radial convexity requires, for every $A\preceq C\preceq B$ in that cone,

$$
\|f(C)-f(A)\|_F\le\|f(B)-f(A)\|_F,
\qquad
\|f(B)-f(C)\|_F\le\|f(B)-f(A)\|_F.
$$

Matrix monotonicity permits either a uniformly increasing or a uniformly decreasing Loewner direction. The functional calculus is spectral calculus; extending the real scalar function away from $(0,\infty)$ does not affect its values on the positive cone. The companion definitions use Mathlib's continuous functional calculus and the Euclidean norm of all entries as the Frobenius norm.

## Repository-derived construction

Set $\varepsilon=1/20000$ and

$$
f(t)=\frac{t+1}{t+3}+\frac{t+1}{2t+4}
-\varepsilon\frac{t+1}{3t+5}.
$$

The order-preserving Cayley map $h(A)=I-2(A+I)^{-1}$ takes the positive cone into $-I\prec X\prec I$. In these coordinates,

$$
f(A)=g(h(A)),\qquad
g(X)=R_2(X)+R_3(X)-\varepsilon R_4(X),\quad R_s(X)=(sI-X)^{-1}.
$$

For $U\preceq V$ in the Cayley interval and $H=V-U$, each endpoint $C\in\{U,V\}$ admits a factorization

$$
R_s(V)-R_s(U)=R_s(C)Z_sR_s(C),\qquad
\tfrac13 H\preceq Z_s\preceq3H.
$$

The lower factor is $H+HR_s(V)H$. The upper factor is
$H^{1/2}(I+H^{1/2}R_s(V)H^{1/2})^{-1}H^{1/2}$. These formulas allow singular $H$.

In dimension three let $y_i=3-\lambda_i(C)>2$, and let $e_j$ be their elementary symmetric functions. With $d=1+e_1+e_2+e_3$, set

$$
c_1=\frac{\prod_i(y_i-1)}d,\quad
c_2=\frac{2(e_2-e_3)}d,\quad c_3=\frac{2e_3}d.
$$

At every spectral node,

$$
R_2R_4=c_1R_2^2+c_2R_2R_3+c_3R_3^2,
\quad
R_3R_4=2c_1R_2^2+(2c_2-1)R_2R_3+2c_3R_3^2.
$$

The bounds $|c_1|\le1$, $|c_2|,|c_3|\le2$ give squared coefficient sums at most $9$ and $45$. Spectral interpolation proves these matrix identities even when eigenvalues coincide. Consequently the two mixed weighted quadratic forms are bounded by $54$ times the sum of the three unmixed forms.

Since $Dg_C(K)=R_2KR_2+R_3KR_3-\varepsilon R_4KR_4$, the endpoint factorizations imply

$$
z^*Dg_C(g(V)-g(U))z\ge
\left(\frac13-324\varepsilon\right)
\sum_{F\in\{R_2^2,R_2R_3,R_3^2\}}\|H^{1/2}Fz\|^2\ge0.
$$

Here $1/3-324/20000=4757/15000>0$. Trace cyclicity makes $Dg_C$ self-adjoint for the Frobenius pairing. Along each ordered segment, differentiating the squared endpoint distance therefore has the required sign. The real mean-value monotonicity theorem yields both radial inequalities over the entire Cayley interval, and the Cayley map transports them to the entire positive cone.

## Exact finite obstruction

Let

$$
A=\operatorname{diag}(1/3,1,3),\quad
B=\frac1{25}\begin{pmatrix}11&4&8\\4&31&12\\8&12&99\end{pmatrix},
\quad v=(-35,48,-15)^T.
$$

Both matrices are positive definite, and $B-A=(2/75)ww^*$ for $w=(2,3,6)^T$. Exact inversion gives

$$
v^*(f(B)-f(A))v=-\frac2{111549375}<0,
\qquad
(f(B)-f(A))_{00}=\frac{1833242113439}{80513884788750}>0.
$$

Thus this same ordered pair excludes both possible monotonicity directions. The certificate uses explicit rational inverse tables; no approximate eigenvalue computation is needed.

## Scope

The paper's Proposition 3.9 supplies the forward implication from matrix monotonicity to radial convexity. Its Theorem 4.11 treats the differentiable order-two converse. Those literature results are contextual and are not reproved by the companion counterexample.

Direct sums of the finite certificate establish failure of matrix monotonicity in every degree at least three. This observation alone does not establish radial convexity in those larger dimensions: the three-node estimate is dimension dependent. Failure of the equivalence in every order at least three and a characterization of radial convexity require further arguments.

## ASSUMED-UNVERIFIED

The supplied preregistration identifies issue #19013 and arXiv:2610.17393v1 as the source. No additional online literature search or worldwide priority claim is established by this offline implementation. The higher-dimensional direct-sum observation is not a theorem in the companion Lean modules.
