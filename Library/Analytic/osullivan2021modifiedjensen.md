---
bibkey: osullivan2021modifiedjensen
authors: Cormac O'Sullivan
year: 2021
title: Zeros of Jensen polynomials and asymptotics for the Riemann xi function
doi: 10.1007/s40687-020-00240-5
url: https://arxiv.org/abs/2007.13582v2
claim: Theorem 3.5 and equation (3.6) give an RH criterion using all zero-shift Hermite combinations; the paper's large-shift sufficient bound does not establish that complete family.
strata_touched: []
license: citation-only
triage: anchor
---

# The modified Hermite–Jensen criterion

The primary is Cormac O'Sullivan, *Zeros of Jensen polynomials and
asymptotics for the Riemann xi function*,
[arXiv:2007.13582v2](https://arxiv.org/abs/2007.13582v2), version submitted
9 December 2020. Journal metadata identifies *Research in the Mathematical
Sciences* **8** (2021), article **46**, DOI
[10.1007/s40687-020-00240-5](https://doi.org/10.1007/s40687-020-00240-5).
The theorem and equation locators below refer to the arXiv version;
the journal metadata does not establish equality of the two texts.
This citation-only input and its parameter applications have no new
Lean certification or originality claim. No source text is vendored.

## Actual coefficients and Hermite convention

Write the source's positive coefficient $\gamma(k)$ as $\Gamma_k$,
to distinguish it from the Euler Gamma function. Equations (1.2)–(1.4)
define

$$
\begin{aligned}
\Theta(z)&=\xi(1/2+\sqrt z)
          =\sum_{k\ge0}\frac{\Gamma_k}{k!}z^k,\\
\Gamma_k&=\frac{k!}{(2k)!}\xi^{(2k)}(1/2),\\
J^{d,n}(X)&=\sum_{j=0}^d\binom dj\Gamma_{n+j}X^j,\\
\mathcal H_{d,n}(X)&=\sum_{j=0}^d\binom dj\Gamma_{n+j}H_{d-j}(X).
\end{aligned}
\tag{MH}
$$

The square-root notation defines an entire function through the even
expansion of $\xi$ about $1/2$; it imposes no branch cut. The source calls
$\mathcal H_{d,n}$ by $P^{d,n}$, distinct from the repository's $P_d$.
The physicists' Hermite convention is

$$
e^{2Xt-t^2}=\sum_{m\ge0}H_m(X)\frac{t^m}{m!},
\qquad
H_m(X)=m!\sum_{r=0}^{\lfloor m/2\rfloor}
        \frac{(-1)^r(2X)^{m-2r}}{r!(m-2r)!}.
\tag{HC}
$$

These are O'Sullivan's coefficients without an additional factor $8$.
The [actual theta correspondence](holland2026jensenwedge.md#correspondence-with-the-actual-theta-coefficients)
already supplies $\Gamma_k=\Xi(0)k!a_k$, with $a_0=1$, from the complete
kernel in [Romik's owning note](romik2021orthogonal.md). That correspondence
and the repository's normalization and primitive interfaces are reused.

## The complete zero-shift family already suffices

In section 3.1, genus $1^*$ means a function of the form
$e^{-az^2}f(z)$ with $a\ge0$ and $f$ entire of genus at most one.
Theorem 3.5 assumes a real entire function $F$ of genus $1^*$ and an
auxiliary nonzero Laguerre–Pólya function $\Omega$. It characterizes
hyperbolicity of $F$ by hyperbolicity of every reciprocal Jensen
polynomial of $F\Omega$. Hyperbolic means that all zeros are real;
it does not require simple zeros.

For $F=\Theta$ and $\Omega=e^{-z^2}$, equation (3.6) identifies the
degree-$d$ reciprocal polynomial as $\mathcal H_{d,0}(x/2)$. The source's
genus condition holds for $\Theta$, which is entire of order $1/2$.
Theorem 3.5 therefore gives the direct specialization

$$
\mathrm{RH}\quad\Longleftrightarrow\quad
\mathcal H_{d,0}\text{ is hyperbolic for every integer }d\ge1.
\tag{ZF}
$$

Theorem 1.2 states the extended criterion with all $d\ge1$ and all
$n\ge0$. For the direct route (ZF), a converse implication from an
individual modified polynomial to an ordinary Jensen polynomial is
unnecessary: the entire zero-shift family is already sufficient.

This family quantifier differs from Corollary 3.8, whose fixed-pair
statement is only

$$
J^{d,n}\text{ hyperbolic}\quad\Longrightarrow\quad
\mathcal H_{d,n}\text{ hyperbolic}.
\tag{FW}
$$

Equations (1.5)–(1.6) exhibit the distinction at degree two:

$$
\begin{aligned}
J^{2,n}\text{ hyperbolic}
&\iff\Gamma_{n+1}^2\ge\Gamma_n\Gamma_{n+2},\\
\mathcal H_{2,n}\text{ hyperbolic}
&\iff\Gamma_{n+1}^2+2\Gamma_n^2\ge\Gamma_n\Gamma_{n+2}.
\end{aligned}
\tag{D2}
$$

The second inequality does not imply the first for general coefficient
triples. This algebraic distinction is not a counterexample for the
actual xi coefficients and does not contradict the full-family criterion.

## Scope of the quantitative sufficient condition

Theorem 1.3 states that, for all sufficiently large $d$,
$\mathcal H_{d,n}$ is hyperbolic whenever

$$
\frac{n}{\log^2 n}\ge\frac{d^{3/4}}2.
\tag{LS}
$$

This is a large-shift result, with its expression used for $n>1$.
It supplies no application at zero shift and no numerical value for the
degree threshold. Moving to a different shift changes the actual
coefficient window $\Gamma_{n+j}$.

Theorem 8.1, attributed to Turán, supplies real simple roots for
$G=\sum_{j=0}^dc_jH_j$ under

$$
\sum_{j=0}^{d-2}2^jj!c_j^2<2^d(d-1)!c_d^2.
$$

Applied to (MH), equation (8.2) is the sufficient budget

$$
\sum_{j=2}^d\frac{d}{2^jj!}\binom dj
       \left(\frac{\Gamma_{n+j}}{\Gamma_n}\right)^2<1.
\tag{TB}
$$

For fixed actual $n\ge0$ and $d\ge2$, its positive $j=2$ term is

$$
\frac{d^2(d-1)}{16}
       \left(\frac{\Gamma_{n+2}}{\Gamma_n}\right)^2.
\tag{FT}
$$

The ratio is fixed and positive, so (FT) grows without bound as $d$
increases. Thus (TB) cannot prove unbounded-degree hyperbolicity at a
fixed shift, including zero. This is a limitation of this sufficient
condition, not nonhyperbolicity of the family or a disproof of RH.

## Exact finite-polynomial correspondence

Reuse the [normalized Jensen tower](../../Blueprint/D5/S3/Zeros/Jensen/NormalizedJensenDegreeLowering.md)
with $P_d(X)=J^{d,0}(X/d)/\Xi(0)$ and its monic reflection
$q_d(x)=x^dP_d(-1/x)$. For $D_x=d/dx$, (HC) gives the finite-polynomial
parameter application

$$
\frac{\mathcal H_{d,0}(-dx/2)}{\Xi(0)(-d)^d}
=\exp(-D_x^2/d^2)q_d(x),\qquad d\ge1.
\tag{HT}
$$

Here the exponential is the finite sum
$\sum_{r=0}^{\lfloor d/2\rfloor}(-1)^rD_x^{2r}/(r!d^{2r})$
on degree-$d$ polynomials. Its sign is part of the convention; its
inverse need not preserve real roots. Equation (HT) identifies a
polynomial transform, not a deformation of the complete Xi kernel
at a physical de Bruijn–Newman time.

For a monic $q_d$ and $d\ge2$, the $x^{d-1}$ coefficient stays fixed
and the $x^{d-2}$ coefficient changes by $-(d-1)/d$. The parameter
$1/d^2\to0$ consequently gives no vanishing coefficient correction
uniformly across these increasing degrees, and by itself gives no
uniform control of their roots.

Equation (ZF) leaves a concrete alternative obligation: control the
actual modified zero-shift family for every degree. A fixed-degree
inference back to $q_d$ would require a separate reverse estimate;
the direct full-family route does not. The source statements and
these parameter applications supply neither that all-degree estimate
nor the complete signed Robin-tail bound.

## Source display limitation

The inspected HTML's intermediate expansion of
$g_d^*(e^{-z^2};x)$ after Theorem 3.5 displays the power $x^{d-r}$.
The definition of the reciprocal Jensen polynomial and (HC) require
$x^{d-2r}$. Equation (3.6) supplies the intended Hermite identity;
the inconsistent intermediate powers are not used. This observation
concerns the HTML display and does not identify an error in the
journal text or establish a PDF comparison.
