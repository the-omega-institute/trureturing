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

## A uniform finite bound for the Selberg coefficients

A bound valid when both $q$ and $X$ vary follows from the same source
without taking its fixed-$q$ asymptotic. Lemma 5.1, equation (5.2), states

$$
|\check m_1^{(1)}(Y)-1|
\le Y^{-1/2}+
\frac{8.55\times10^{-6}\,\mathbf1_{Y\ge10^{12}}}{\log Y}.
$$

For $1\le Y<10^{12}$ this implies $|\check m_1^{(1)}(Y)|\le2$;
for $Y\ge10^{12}$ the displayed error is less than one. For $0<Y<1$
the defining sum is empty. Lemma 7.1 and equation (7.6) give the
positive-coefficient convolution, and Lemma 7.2(a) evaluates its total:

$$
\check m_q^{(1)}(X)=\sum_{d\mid q^\infty}\frac1d\,
\check m_1^{(1)}(X/d),\qquad
\sum_{d\mid q^\infty}\frac1d=\frac q{\varphi(q)}.
$$

Consequently $|\check m_q^{(1)}(X)|\le2q/\varphi(q)$ for every
$q\ge1,X>0$, with the same constant. The Selberg-frequency
[application](../Weil/corvalan2023interpolation.md) uses
$X=N/q$ and $b_{N,q}=\mu(q)\check m_q^{(1)}(N/q)/\log N$ for
squarefree $q$. This is a uniform coefficient allowance, including
short sums near $q=N$, not a bound for their finite-interval signed
quadratic correlations. These are consequences of the cited paper
inputs; no new supplier theorem or Lean verification is claimed.

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

## The centered error at a growing prime prefix

For the same $P_z$, $E_z$ and $C_z$ used by the
[actual-kernel application](ramarezuniga2026identityfactory.md#the-actual-logarithmic-scale-curvature-and-centered-second-abel-formula),
put $L=\log z$ and
$\varepsilon_z(r)=\check m_{P_z}^{(1)}(e^r)-C_z$.
The source's equation (7.4) gives $Q_{1,P_z}=C_z$ exactly.
Corollary 7.5, not a new asymptotic theorem, therefore supplies

$$
|\varepsilon_z(r)|\le
R_{1/2}(z)e^{-r/2}
+\frac{8.55\times10^{-6}}r R_\theta(z)
\mathbf1_{r\ge12\log10},\qquad r>0,
$$

$$
R_\alpha(z)=\prod_{p\le z}(1-p^{-\alpha})^{-1},\qquad
\theta=1-\frac1{12\log10}.
$$

This is a useful fixed-$z$ error bound. Its modulus factors cannot be
replaced by constants independent of the prime prefix. For fixed
$0<\alpha<1$, the global prime-count lower bound in
[Rosser–Schoenfeld, Corollary 1](../Arith/rosser1962approximate.md#global-prime-counts-and-the-classical-pnt-interface)
gives, for $z\ge17$,

$$
\log R_\alpha(z)\ge\sum_{p\le z}p^{-\alpha}
\ge z^{-\alpha}\pi(z)>\frac{z^{1-\alpha}}{\log z}.
$$

Consequently, for each fixed $u>0$, both
$R_{1/2}(z)z^{-u/2}$ and $R_\theta(z)/(u\log z)$ tend to infinity.
Thus the displayed numerical allowance is not a small-error estimate
at $e^r=z^u$. This is a statement about that allowance, not a lower
bound for the actual error or a failure of the cited theorem.

The actual error has an elementary, different behavior on the unit
range. For $0\le r\le L$, the only integer at most $e^r$ coprime to
$P_z$ is one. Hence

$$
\check m_{P_z}^{(1)}(e^r)=r,\qquad
\varepsilon_z(r)=r-C_z<0.
$$

The strict sign follows without an asymptotic estimate: the complete
positive smooth reciprocal sum $C_z$ contains every $n\le\lfloor z\rfloor$,
so $C_z\ge H_{\lfloor z\rfloor}>\log z$. The classical prime-product
bounds in [Rosser–Schoenfeld, Theorem 8](../Arith/rosser1962approximate.md)
also give, for each fixed $0\le u\le1$,

$$
\frac{\varepsilon_z(uL)}L\longrightarrow u-e^\gamma<0.
$$

This unit-range component cannot be modeled as an error vanishing
uniformly with the growing filter. Its source is retained explicitly
in the complete centered Abel formula; it does not determine the
complementary range's sign. For all $r\ge0$, the already available
uniform inequality $0\le\check m_{P_z}^{(1)}(e^r)\le2C_z$ does give
$|\varepsilon_z(r)|\le C_z$, but this constant envelope is not
integrable against the whole actual curvature, whose fixed-$z$
behavior is $\mathcal G_{z,x}''(r)\sim E_z(1)/r$.

The two envelopes have distinct uses: the explicit decaying error
pays fixed-filter convergence; the uniform coefficient bound pays
finite intervals. Neither separately pays the signed integral with
a growing filter, its affine endpoints and the original unit head.
That common-filter estimate remains an additional obligation.


The exact joint real-axis alternative in the
[actual-kernel application](ramarezuniga2026identityfactory.md#exact-real-axis-payment-of-the-truncated-centered-tail)
pairs this same centered error before applying an absolute envelope.
It expresses the whole tail using finite prefix data and one combined
$\zeta/E_z$ bracket, with both zero-end cancellations retained. The
associated prime-resolution law transfers equal and opposite amounts
between the auxiliary full pair and its original-source compensation.
These applications do not turn either pointwise allowance into a
uniformly vanishing error; the full same-integer Robin lower bound is
still required.
