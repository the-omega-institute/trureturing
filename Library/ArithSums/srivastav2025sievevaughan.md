---
bibkey: srivastav2025sievevaughan
authors: Priyamvad Srivastav
year: 2025
title: Log-free bounds on exponential sums over primes
doi: null
url: https://arxiv.org/abs/2505.07803v2
claim: The sieve-weighted Vaughan identity retains exact von Mangoldt recovery for general normalized sieve weights by preserving extra convolution terms; the stated additive exponential-sum bound supplies no centered signed Robin-tail estimate at zero frequency.
strata_touched: []
license: citation-only
triage: anchor
---

# Exact recovery with sieve weights and the remaining signed estimate

The inspected primary is [arXiv:2505.07803v2](https://arxiv.org/html/2505.07803v2),
revised 27 January 2026; v1 was submitted 12 May 2025. The locators below
refer to v2. This note attributes the source's results and records their
parameter correspondence; it supplies neither an independent proof audit
nor Lean certification. The published identities and sieve arguments are
reused, not new project mathematics.

## The recovery operator includes additional convolutions

Write $*$ for Dirichlet convolution and $\mathbf 1(n)=1$ for $n\ge1$.
Juxtaposition of arithmetic functions means pointwise multiplication.
Section 2, Lemma 2.1 and its first Remark allow arbitrary weights with

$$
\lambda(1)=1,\qquad \theta+\theta'=\mu.
$$

With the source's least-common-multiple transform

$$
h(d)=\sum_{[d_1,d_2]=d}\lambda(d_1)\theta'(d_2),
$$

and $V>1$, the cited identity is

$$
\Lambda
=h*\log-\mathbf 1*h*\Lambda_{\le V}
 +\bigl[(\mathbf 1*\theta)(\mathbf 1*\lambda)\bigr]*\Lambda_{>V}
 +\Lambda_{\le V}.
\tag{SV1}
$$

Here $\Lambda_{\le V}$ and $\Lambda_{>V}$ truncate the complete
von Mangoldt function, including prime powers. The source also states
the corresponding identity for $\mu$. Its standard weight choice has
$1<U<U_1$, $R>1$, with $\theta'$ supported on $d\le U_1$ and
$\lambda$ on $d\le R$; consequently $h$ is supported on $d\le U_1R$.
The first Remark explicitly permits other normalized weight choices.

This recovery operator differs from requiring
$\sum_{d\mid m}a(d)=\Lambda(m)$ for a single coefficient vector $a$.
A restriction proved for that simple divisor response would not exclude
(SV1). Optimizing sieve weights and retaining exact recovery are compatible
in this published formulation, provided all additional terms are kept.
Those terms have no favorable sign asserted by Lemma 2.1.

## The divisor-to-frequency expansion is already supplied

The weights in equation (2.1) are

$$
\lambda(d)=\frac{d\mu(d)}{\varphi(d)}
 \frac{G_{qd}(R/d)}{G_q(R)}\mathbf 1_{(d,q)=1},
\qquad
G_\ell(x)=\sum_{\substack{r\le x\\(r,\ell)=1}}
 \frac{\mu(r)^2}{\varphi(r)}.
$$

Section 5.1, Lemma 5.1 gives, for every integer $n\ge1$,

$$
G_q(R)\sum_{d\mid n}\lambda(d)
=\sum_{\substack{r\le R\\(r,q)=1}}
 \frac{\mu(r)}{\varphi(r)}c_r(n),
\qquad
c_r(n)=\sum_{\substack{a\bmod r\\(a,r)=1}}e^{2\pi i an/r}.
\tag{SV2}
$$

The paper attributes this Selberg-weight/Ramanujan-sum connection to
Kobayashi and Huxley. The cited predecessors are Kobayashi,
*A note on the Selberg sieve and the large sieve*, Proc. Japan Acad. 49
(1973), 1–5, and Huxley, *The distribution of prime numbers* (1972).
Their full texts were not independently inspected here.

Thus an existing source supplies this particular transition from divisor
responses to additive frequency channels. It is not a new FIB spectral
theorem. Neither (SV1) nor (SV2) identifies these additive frequencies
with the nontrivial zeros of the Riemann zeta function or transports the
five Zeckendorf occupancy classes to the needed arithmetic amplitudes.

## The exponential-sum theorem keeps its original parameters

To distinguish the paper's small parameter from the Robin excess exponent,
write it as $\kappa$. Theorem 1 assumes $0<\kappa\le1/10$, sufficiently
large $x\ge x_0(\kappa)$, and

$$
u=\frac aq+\frac\delta x,\qquad (a,q)=1,
\qquad |\delta|\le\frac{x^{1/5+\kappa}}q,
\qquad 1\le q\le x^{2/5-\kappa},
\qquad \delta_0=\max\{1,|\delta|/4\}.
$$

It states the uncentered bound

$$
\left|\sum_{n\le x}\Lambda(n)e^{2\pi i nu}\right|
\le\frac q{\varphi(q)}
 \mathscr F_\kappa\!\left(
 \frac{\log(\delta_0q)}{\log x},
 \frac{\log^+(\delta_0/q)}{\log x}\right)
 \frac{x}{\sqrt{\delta_0q}},
\tag{SV3}
$$

with $\mathscr F_\kappa$ specified in equation (1.4) and
$\log^+z=\max\{\log z,0\}$. The theorem also bounds the corresponding
Möbius exponential sum. The Remarks explicitly include $q=1$ and $q=2$.
The source calls the result semi-explicit: $x_0(\kappa)$ is effectively
computable but is not given as a numerical threshold.

For the Robin Chebyshev sum, the additive frequency is $u=0$, represented
by $a=0$, $q=1$, $\delta=0$. Here $\delta_0=1$ and the two arguments of
$\mathscr F_\kappa$ are zero. The cited theorem bounds the uncentered
$\psi(x)$; it states no estimate for the centered difference
$\psi(x)-x$ at this frequency. Its nonzero-frequency savings cannot be
substituted for the original signed tail merely by changing coordinates.
