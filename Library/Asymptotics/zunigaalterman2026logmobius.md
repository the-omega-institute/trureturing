---
bibkey: zunigaalterman2026logmobius
authors: Sebastian Zuniga-Alterman
year: 2026
title: "A recurrence in logarithmic Möbius sums with coprimality conditions via Euler–Maclaurin"
doi: null
url: https://arxiv.org/abs/2610.17720v1
claim: "Theorem 1.1 gives explicit q-dependent polynomial approximations for logarithmically weighted coprime Möbius sums, and Theorem 1.2 proves nonnegativity of the reciprocal-divisor weighted family for positive logarithmic order; neither theorem supplies the same-candidate Robin budget needed for the FIB family."
strata_touched: []
license: citation-only
triage: anchor
---

# Logarithmic Möbius sums with coprimality conditions

The source is [arXiv:2610.17720v1](https://arxiv.org/pdf/2610.17720v1), submitted 13 October 2026. The paper is a preprint; its proofs and constants were not independently audited here, and no Lean verification is claimed.

For $X>0$, $k\ge0$ and $q\ge1$, equation (1.1) defines

$$
\check m_q^{(k)}(X)
 =\sum_{\substack{n\le X\\(n,q)=1}}
   \frac{\mu(n)}n\log^k\!\left(\frac Xn\right),
\qquad
\widetilde m_q^{(k)}(X)
 =\sum_{\substack{n\le X\\(n,q)=1}}
   \frac{\mu(n)}{\sigma(n)}\log^k\!\left(\frac Xn\right).
$$

Theorem 1.1 states that each family is approximated by a degree $k-1$ polynomial in $\log X$ (zero polynomial for $k=0$), with explicit constants depending only on $k$. The first error has the form

$$
\left|\check m_q^{(k)}(X)-Q_{k,q}(\log X)\right|
\le
\frac{\sqrt q}{\varphi_{1/2}(q)}\frac{A_k}{\sqrt X}
+
\frac{q^\theta}{\varphi_\theta(q)}
\frac{B_k\mathbf 1_{X\ge10^{12}}}{\log X},
\qquad
\theta=1-\frac1{12\log 10},
$$
with an analogous explicit bound for $\widetilde m_q^{(k)}$ using the source's multiplicative factor $\mathpzc p_s(q)$ and numerical constants $3.575$ and $1.693$. For fixed $k,q$, both remainders tend to zero as $X\to\infty$.

Theorem 1.2 proves

$$
\widetilde m_q^{(k)}(X)\ge0
$$
for every $k,q\ge1$ and $X>0$. This is a logarithmically smoothed sign result. The corresponding unsmoothed sum $\check m_q^{(0)}(X)=\sum_{(n,q)=1,n\le X}\mu(n)/n$ may change sign, so the theorem does not give a sign for order zero.

## Boundary for the FIB Robin route

The reciprocal-divisor weight is related to the project's arithmetic vocabulary, but the source sum is Möbius signed and truncated at $X$. The Robin quantity

$$
Z(N)=\frac{\sigma(N)}N=\sum_{d\mid N}\frac1d
$$

is a positive divisor sum at one fixed integer. The paper does not turn $\widetilde m_q^{(k)}(X)$ into an upper bound for this point value, nor does it control the joint low- and high-loss divisor budget

$$
C_*+H_*
$$

for the same FIB candidate $N_*=1+F_rg$.

A FIB congruence or a fixed forbidden-prime set can supply a particular coprimality parameter $q$, but it does not supply the required correspondence between the recursive address, the cutoff $X$, the logarithmic order $k$, and every divisor of $N_*$. The explicit $q$-dependence is therefore a possible input to a future common-candidate estimate, not that estimate itself. This card records the interface and its failure boundary so that later Robin/FIB searches do not repeat this route.
