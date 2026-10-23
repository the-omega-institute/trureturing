---
bibkey: bondarenko2018pseudomoments
authors: Andriy Bondarenko, Ole Fredrik Brevig, Eero Saksman, Kristian Seip, and Jing Zhao
year: 2018
title: Pseudomoments of the Riemann zeta function
doi: null
url: https://arxiv.org/abs/1701.06842v3
claim: Classical generalized divisor coefficients realize the leading golden-ratio constant in the existing joint modal entropy and complete Mangoldt charge bound. This is a source-specific paper application, without a full Weil sharpness, minimizer, RH, Robin, or Lean certification claim.
strata_touched: []
license: bibliographic-reference-only
triage: anchor
---

# Generalized divisor weights saturate the joint modal bound

## Classical inputs and the actual remaining question

The inspected primary is [arXiv:1701.06842v3](https://arxiv.org/abs/1701.06842v3),
version 1 June 2018, available as [PDF](https://arxiv.org/pdf/1701.06842v3)
and [HTML](https://arxiv.org/html/1701.06842v3). Section 2, printed p.5,
equations (8), (10) and (11), supplies the real-parameter coefficients
$d_k$, their prime-power values and submultiplicativity, including
arguments with common prime factors. Printed p.7, equation (18), gives

$$
\sum_{n\le x}d_\alpha(n)
=\frac{x(\log x)^{\alpha-1}}{\Gamma(\alpha)}
 +O_\alpha\bigl(x(\log x)^{\alpha-2}\bigr)
$$

for fixed $\alpha\ge1$, citing the classical Selberg--Delange method and
Tenenbaum, Chapter II.5. These are `literature-attested` inputs. The
harmonic asymptotic for $d_k^2$ below is an Euler-factor application of
that input; it is not quoted as a displayed theorem of this paper.

The [existing actual-source bound](suzuki2026screw.md#pay-modal-entropy-and-arithmetic-charge-before-separating-them),
W285 and W303--W306, already owns the full Mangoldt convolution identity,
weighted Schur estimate and Gibbs cancellation. For $L\ge2$, write

$$
(C_La)_n=\sum_{\substack{q\mid n\\q\ge2}}
\frac{\Lambda(q)}{\sqrt q}\,a_{n/q},\qquad
p_n=\frac{|a_n|^2}{\|a\|_2^2},\qquad
H(p)=-\sum_{n\le L}p_n\log p_n.
$$

Its existing estimate is

$$
J_L(a):=H(p)+\frac{\langle a,(C_L+C_L^*)a\rangle}{\|a\|_2^2}
\le\varphi\log L+\log\mathcal H_L+C,
\qquad
\mathcal H_L=\sum_{n\le L}\frac1n,
\quad\varphi=\frac{1+\sqrt5}{2}.
\tag{B1}
$$

The following `repo-derived` application determines the leading
coefficient of this joint observable, including actual source
realization. It reuses (B1), without another proof of its upper bound.
It makes no claim to literature priority and has not been Lean checked.

## One common vector attains the leading coefficient

Fix $1<k\le2$ and use the classical positive coefficients

$$
a_n=\frac{d_k(n)}{\sqrt n},\qquad
d_k(p^j)=\frac{(k)_j}{j!},\qquad
Z_k(L)=\sum_{n\le L}\frac{d_k(n)^2}{n},\qquad
p_n=\frac{d_k(n)^2}{nZ_k(L)}.
\tag{B2}
$$

The complete logarithmic-derivative convolution already cited in W306
is exact at every $n\le L$:

$$
\sum_{q\mid n}\Lambda(q)d_k(n/q)
=\frac{\log n}{k}d_k(n).
$$

Consequently

$$
(C_La)_n=\frac{\log n}{k}a_n,\qquad
\frac{\langle a,(C_L+C_L^*)a\rangle}{Z_k(L)}
=\frac2k\,\mathbb E_p\log n.
\tag{B3}
$$

This is a diagonal identity on this vector, not an eigenvalue equation
with a constant eigenvalue. All prime powers and shared prime factors
are retained; no prime-only replacement is made.

For completeness, the parameter correspondence for the classical mean
value input is

$$
\sum_{n\ge1}\frac{d_k(n)^2}{n^s}
=\zeta(s)^{k^2}G_k(s),\qquad
G_k(s)=\prod_p(1-p^{-s})^{k^2}
\sum_{j\ge0}\frac{d_k(p^j)^2}{p^{js}}.
\tag{B4}
$$

Each local factor is $1+O_k(p^{-2\Re s})$ away from finitely many
small primes, so $G_k$ has an absolutely convergent Dirichlet series in
$\Re s>1/2$. In particular its coefficients $g_k$ satisfy
$\sum|g_k(n)|/n<\infty$, $d_k^2=d_{k^2}*g_k$, and

$$
G_k(1)=\prod_p(1-p^{-1})^{k^2}
\sum_{j\ge0}\frac{d_k(p^j)^2}{p^j}>0.
$$

Partial summation of the cited equation (18), with $\alpha=k^2$,
gives $\sum_{n\le x}d_{k^2}(n)/n\sim
(\log x)^{k^2}/\Gamma(k^2+1)$. Convolution with $g_k$ and dominated
convergence therefore give

$$
Z_k(L)\sim c_k(\log L)^{k^2},\qquad
c_k=\frac{G_k(1)}{\Gamma(k^2+1)}>0.
\tag{B5}
$$

The domination uses the same harmonic sum bounded by
$C_k(1+\log x)^{k^2}$ and $\sum|g_k(n)|/n<\infty$.
No new general Selberg--Delange theorem is needed. Another partial
summation gives

$$
\mathbb E_p\log n
=\log L-\frac1{Z_k(L)}\int_1^L Z_k(t)\frac{dt}{t}
=\frac{k^2}{k^2+1}\log L+o_k(\log L).
\tag{B6}
$$

The entropy of the same distribution is exactly

$$
H(p)=\log Z_k(L)+\mathbb E_p\log n
       -2\mathbb E_p\log d_k(n).
\tag{B7}
$$

For $1<k\le2$, the prime-power coefficients give
$1\le d_k(n)\le d_2(n)=\tau(n)$. The classical divisor bound already
used in W295 implies, for every fixed $\varepsilon>0$,

$$
0\le\mathbb E_p\log d_k(n)
\le\varepsilon\log L+C_\varepsilon.
$$

Thus this expectation is $o_k(\log L)$, while
$\log Z_k(L)=O_k(\log\log L)$. Combining (B3), (B6) and (B7) yields

$$
\frac{J_L(a)}{\log L}\longrightarrow
\frac{k^2+2k}{k^2+1}.
\tag{B8}
$$

The derivative of this last rational function has the sign of
$1+k-k^2$. Its maximum on $1<k\le2$ is attained at $k=\varphi$
and equals $\varphi$. Together with the existing upper bound (B1),
this gives the paper-level sharpness statement

$$
\lim_{L\to\infty}\frac1{\log L}
\sup_{a\in\mathbb C^L\setminus\{0\}}J_L(a)=\varphi.
\tag{B9}
$$

No coefficient $c<\varphi$ can replace $\varphi$ in a bound uniform
over this full vector class with a uniform $o(\log L)$ remainder.
The sharpness of the smaller-order terms is not determined.

## Realize the vector in the owned source domain

Retain W285's actual profiles
$h_n(y)=\sum_{d\mid n}g_d(y)$ and
$a_n(y)=y^{9/4}h_n(y)/\sqrt n$.
For each $L$, put $R_L=\pi(L+1/2)^2$, choose
$0<\delta\le1$, and take a common nonzero
$g\in C_c^\infty(I_L)$, where $I_L=(R_L,R_L+\delta)$.
Then $N(y)=\lfloor\sqrt{y/\pi}\rfloor=L$ throughout $I_L$.
With $D=\{1,\ldots,L\}$ choose

$$
g_d(y)=d_{k-1}(d)g(y),\qquad
f_L(x)=\sum_{d\le L}d^4g_d(d^2x).
\tag{B10}
$$

The same Euler coefficient definition is valid for $k-1>0$.
The classical convolution $1*d_{k-1}=d_k$ gives

$$
h_n(y)=d_k(n)g(y),\qquad
a_n(y)=y^{9/4}g(y)\frac{d_k(n)}{\sqrt n}.
\tag{B11}
$$

The common positive integral factor cancels from both the modal
probabilities and the normalized complete charge. They are exactly
(B2) and (B3). This is simultaneous attainment on one actual profile,
not a combination of separate marginal optimizers. Therefore the
same leading sharpness holds in the unrestricted actual modal class.
The owned finite Gaussian recovery applies for each fixed tuple;
no common recovery start as $L\to\infty$ is asserted.

## Consequence and retained boundary

The unrestricted joint coefficient in W306 cannot be lowered below
$\varphi$. An improvement must use additional constraints on the actual
profiles or another estimate that couples the remaining terms.
This does not prove the full exponent $\kappa_0=1-\varphi/2$ in
W303--W304 optimal: the other debits and positive terms have not been
shown to saturate together.

The family (B10) is not asserted to have a uniformly bounded normalized
sixth moment or to consist of negative minimizers. It therefore does
not obstruct estimates that exploit the actual fixed-cap minimizing
class. No negative-energy direction, improved strict Robin bound,
all-source Weil positivity, RH proof or Lean/kernel certificate is
supplied by (B9).
