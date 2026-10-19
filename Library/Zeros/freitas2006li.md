---
bibkey: freitas2006li
authors: Pedro Freitas
year: 2006
title: A Li-type criterion for zero-free half-planes of Riemann's zeta function
doi: 10.1112/S0024610706022599
url: https://arxiv.org/abs/math/0507368v1
claim: Freitas supplies the normalized generalized Li coefficients and their generating-function interface; a uniform finite signed transfer approximates the actual critical Fibonacci matrix from the unconditional tau equal to two data, without transferring positivity.
strata_touched: []
license: citation-only
triage: anchor
---

# Generalized Li data and a signed return to the critical matrix

The primary is Pedro Freitas,
[arXiv:math/0507368v1](https://arxiv.org/abs/math/0507368v1), version
18 July 2005, preceding the publication in *Journal of the London
Mathematical Society* 73(2), 399--414 (2006). The locators below refer to
this preprint; the DOI supplies publication metadata. The source's
criterion, generating-function interface and differential system are
existing results, not new parts of the Fibonacci model. The application
below controls approximation error, without a new bound on the critical
signed probes, Lean certification or a priority claim.

## TL1. Exact normalization and an existing analytic interface

Freitas's definition (1.3) and Lemma 3.1 use

$$
\alpha_n(\tau)=\frac1\tau\Lambda_n(\tau),\qquad
\Lambda_n(\tau)=\lim_{T\to\infty}
\sum_{\substack{\rho\in Z(\zeta)\\|\Im\rho|\le T}}
\left[1-\left(\frac\rho{\rho-\tau}\right)^n\right].
$$

Symmetric zero pairing agrees with the real conjugate-paired limit.
Functional symmetry gives $\Lambda_n(1)=\lambda_n$, the original
classical coefficient. Theorem 1 gives the zero-free half-plane
criterion and, unconditionally, $\alpha_n(\tau)\ge0$ for $\tau\ge2$.
Theorem 4.3, equation (4.1), already gives the differential system;
in the unnormalized convention it is
$\tau\partial_\tau\Lambda_n=n(\Lambda_{n+1}-\Lambda_n)$.
These results are reused, not re-proved.

Choose compatible local logarithms and write
$L_\tau(z)=\log\xi(\tau/(1-z))$. The exact parameter application of
Lemma 3.1(ii) is

$$
L_\tau(z)-L_\tau(0)
=\sum_{n\ge1}\frac{\Lambda_n(\tau)}n z^n.
\tag{TL1}
$$

The conventional constant factor in $\xi$ changes only the constant
term. In particular $L_2$ has a holomorphic logarithm on $|z|<1$, since
$\Re(2/(1-z))>1$ there. Use the actual nonnegative coefficients
$\Lambda_m(2)$ and the published bound
$\Lambda_m(2)=O(m\log(m+1))$ supplied by
[Palojärvi's Theorem 2.1](palojarvi2020tauli.md).

## TL2. A signed boundary re-expansion

For $0<r<1$ put $v_r=2r/(1+r)$ and $\tau_r=2/(1+r)$. Near $z=0$,

$$
L_2(r(2z-1))=L_{\tau_r}(v_rz).
$$

The left-hand Taylor series converges absolutely when
$r(1+2|z|)<1$. Taking the coefficient of $z^n/n$ in TL1 gives the
exact identity

$$
S_n(r):=\sum_{m\ge n}2^n(-1)^{m-n}
\binom{m-1}{n-1}r^m\Lambda_m(2)
=v_r^n\Lambda_n(\tau_r).
\tag{TL2}
$$

The polynomial bound on $\Lambda_m(2)$ also proves absolute convergence
for each fixed $r<1$ and $n$. The limit $S_n(r)\to\lambda_n$ for fixed
$n$ as $r\uparrow1$ is a boundary re-expansion, not a positivity
transport or a uniform estimate for growing $n$.

## TL3. One common finite transfer with uniform error

For each integer $c\ge1$ prescribe

$$
q_c=e^{-c^2},\qquad r_c=1-q_c,\qquad
M_c=\left\lceil e^{2c^2}\right\rceil,
$$

and use the same actual data, regularization and integer cutoff for
all $1\le n\le c$:

$$
A_n(c)=\sum_{m=n}^{M_c}2^n(-1)^{m-n}
\binom{m-1}{n-1}r_c^m\Lambda_m(2).
\tag{TL3}
$$

There are constants $C,c_0$ independent of $n,c$ such that

$$
\boxed{\max_{1\le n\le c}|A_n(c)-\lambda_n|
\le C e^{-c^2/2},\qquad c\ge c_0.}
\tag{TL4}
$$

Here is the uniform parameter argument. Since $\xi(1)\ne0$, one fixed
zero-free complex neighborhood of $1$ supplies $\eta>0$, $0<R_0<1$
and bounded compatible logarithms for $1\le\tau\le1+\eta$,
$|z|\le R_0$. Cauchy estimates for TL1 and its $\tau$ derivative give

$$
|\Lambda_n(\tau)|\le B_0 nR_0^{-n},\qquad
|\partial_\tau\Lambda_n(\tau)|\le B_1 nR_0^{-n}.
$$

As $\tau_{r_c}-1=1-v_{r_c}=q_c/(2-q_c)\le q_c$, all large $c$ have

$$
|S_n(r_c)-\lambda_n|
\le q_c(B_1n+B_0n^2)R_0^{-n}
\le C_1c^2R_0^{-c}e^{-c^2}
\le C_2e^{-c^2/2},\qquad 1\le n\le c.
$$

The zero-free neighborhood is local at the nonzero point $1$; no
zero-free critical strip or RH premise has been introduced.

For the omitted series, the published growth supplier implies
$\Lambda_m(2)\le C_3m^2$. If $m>M_c$ and $1\le n\le c$, the absolute
summand of TL2 is at most
$C_3 2^c m^{c+1}e^{-q_cm}$. Uniformly for $m\ge M_c$ and all
sufficiently large $c$,

$$
c\log2+(c+1)\log m\le q_cm/2.
$$

Indeed, dividing by $m$ and using decreasing $\log m/m$ bounds the
left side divided by $m$ by
$M_c^{-1}[c\log2+(c+1)\log M_c]=O(c^3e^{-2c^2})=o(q_c)$.
Thus the whole omitted series is at most

$$
C_3\sum_{m>M_c}e^{-q_cm/2}
\le4C_3q_c^{-1}e^{-q_cM_c/2}
\le4C_3e^{c^2-e^{c^2}/2}
\le C_4e^{-c^2/2}.
$$

The denominator bound uses $1-e^{-q_c/2}\ge q_c/4$. Combining this with
the regularization error proves TL4. This is a paper application of
the existing analytic and polynomial suppliers. The constants are
existential, the cutoff is large, and no efficient computation,
numerical execution or cutoff optimization is asserted.

## TL4. The same Fibonacci consumer and its unpaid sign

For the original adjacent Fibonacci $a,b,c=a+b$, let $K_j^A$ be the
original real matrix with $\lambda_a,\lambda_b,\lambda_c$ replaced by
$A_a(c),A_b(c),A_c(c)$. TL4 and the row-sum bound give

$$
\boxed{\|K_j^A-K_j\|_{\rm op}\le5Ce^{-c^2/2}}
\quad\text{for every sufficiently large }j.
\tag{TL5}
$$

These are the entire actual Li coefficients of the same $\xi$;
this representation drops no arithmetic channel. It can be combined
with the existing $o(c)$ transfer from the
[actual arithmetic middle](coffey2009stieltjes.md#cs9-a-classical-bound-pays-the-growing-low-prime-prefix).
It does not bound either of the signed probes in CS29.

For comparison, the same-shaped matrix built from $\Lambda_b(2)$ and
$\Lambda_c(2)$ is unconditionally positive semidefinite. For each
$z_\rho=\rho/(\rho-2)$, the classical Poisson probability on the unit
circle has cosine moments $\Re z_\rho^k$. Its real Gram matrix on
$(1-e^{ib\theta},1-e^{ic\theta})$ has entries
$2(1-\Re z_\rho^b)$, $2(1-\Re z_\rho^c)$ and
$1-\Re z_\rho^b-\Re z_\rho^c+\Re z_\rho^{c-b}$.
Finite symmetric zero sums are positive semidefinite; the convergent
coefficient limit gives the asserted comparison matrix. This applies
the classical Poisson identity, rather than inferring a matrix sign
from scalar positivity.

The inversion in TL3 has signed weights. Set
$w_{n,m}=2^n(-1)^{m-n}\binom{m-1}{n-1}r_c^m$ for $m\ge n$, and zero
otherwise. The exact original matrix map gives
$K_j^A=\sum_{m=1}^{M_c}\Lambda_m(2)W_m$.
Already at $m=a<b<c$ its coefficient matrix is

$$
W_a=\begin{pmatrix}0&-w_{a,a}\\-w_{a,a}&0\end{pmatrix},
\qquad w_{a,a}=2^ar_c^a>0.
$$

It has eigenvalues $\pm w_{a,a}$. Hence this representation supplies
no termwise positive semidefinite comparison. This does not assert
that the total $K_j^A$ is nonpositive or that all joint information
in the $\tau=2$ data is insufficient. The remaining task is a signed
bound on the actual common sequence in TL3, strong enough for the
original probes. The approximation bound supplies no such bound;
Robin, endpoint half-variance and RH remain unresolved.
