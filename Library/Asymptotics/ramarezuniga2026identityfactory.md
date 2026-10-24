---
bibkey: ramarezuniga2026identityfactory
authors: Olivier Ramaré and Sebastian Zuniga-Alterman
year: 2026
title: "Möbius function and primes: an identity factory with applications"
doi: 10.1090/mcom/4216
url: https://arxiv.org/abs/2312.05138v3
claim: "Theorems 1.1–1.2 supply a finite weighted identity and uniform coprime logarithmic Möbius positivity; the actual filtered Robin kernel has a positive logarithmic-scale curvature and an exact centered second-Abel application, while its growing-filter signed estimate remains open."
strata_touched: []
license: citation-only
triage: anchor
---

# Weighted Möbius identities and the actual Robin kernel

Ramaré–Zuniga-Alterman's [arXiv:2312.05138v3](https://arxiv.org/html/2312.05138v3)
contains the source statements below. Version 3 was submitted 12 January
2026; the publication DOI is [10.1090/mcom/4216](https://doi.org/10.1090/mcom/4216).
The statements and the parameter correspondence are documentary reuse;
no new supplier theorem, complete proof audit or Lean verification is claimed.

## Uniform logarithmic positivity

For integers $q,k\ge1$, real $\sigma\ge1$ and real $X\ge1$, Theorem 1.2 states

$$
0\le
\sum_{\substack{n\le X\\(n,q)=1}}
\frac{\mu(n)}{n^\sigma}\log^k(X/n)
\le
C_k\frac q{\varphi(q)}
\bigl[k+(\sigma-1)\log X\bigr](\log X)^{k-1},
$$

where $C_1=1.00303$ and $C_k=1$ for $k>1$. For $k=1$ the last
power is the constant one, including at $X=1$. This estimate permits
$q$ and $X$ to vary together; its $q/\varphi(q)$ factor remains part of
the allowance. It does not assert a sign at logarithmic order zero.
The [separate recurrence source](zunigaalterman2026logmobius.md)
already supplies the recorded reciprocal-$\sigma(n)$ positivity,
fixed-$q$ approximations and uniform Selberg coefficient allowance.
Those results need no new proof or renamed wrapper here.

## The finite identity with its endpoint

For arithmetic functions $f,g$, write
$S_f(u)=\sum_{n\le u}f(n)$ and use Dirichlet convolution $f*g$.
Theorem 1.1 assumes $h:(0,1]\to\mathbb C$ is Lebesgue-integrable
on every compact subinterval and $H:[1,\infty)\to\mathbb C$ is
absolutely continuous on every finite interval. For every real $X\ge1$,
its equation (2) is

$$
\begin{aligned}
\sum_{n\le X}f(n)H(X/n)-H(1)S_f(X)
={}&\int_1^X S_{f*g}(X/t)h(1/t)\frac{dt}{t}\\
&+\int_1^X S_f(X/t)
\left[H'(t)-\frac1t\sum_{n\le t}g(n)h(n/t)\right]dt.
\end{aligned}
$$

The endpoint $H(1)S_f(X)$ is explicit. The theorem gives an identity
for a chosen weight; it supplies no automatic sign for the second
integral and no automatic infinite-cutoff limit.

For the harmonic Möbius choice used in the source's proof of
Theorem 1.4, set

$$
f_q(n)=\frac{\mu(n)}n\mathbf1_{(n,q)=1},\qquad
 g(n)=\frac{(-1)^{n+1}}n,\qquad
 m_q(u)=S_{f_q}(u).
$$

Lemma 6.1(ii)–(iii) gives the complete convolution prefix

$$
S_{f_q*g}(u)=A_q(u),\qquad
A_q(u)=\sum_{\substack{u/2<\ell\le u\\\ell\mid q^\infty}}\frac1\ell.
$$

Here $\ell\mid q^\infty$ means that every prime divisor of $\ell$
divides $q$; $\ell=1$ is included when it meets the interval condition.
This is the published alternating-convolution input, not a new
rough-prefix estimate. Theorems 1.4–1.5 keep an error involving
$\int_1^X|m_q(t)|dt$; their special power/logarithmic weights do not
remove that requirement for an arbitrary $H$.

## Parameters needed for the filtered Robin weight

Use the actual definitions in
[the FIB volume, §§428, 434–435](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md):

$$
P_z=\prod_{p\le z}p,\qquad
\eta_z(y)=\sum_{d\mid P_z}\mu(d)\eta(y/d),\qquad
\eta(y)=\log(\lfloor y\rfloor!)-y\log y+y,
$$

$$
P_x^{\eta_z}(s)=\int_x^\infty\eta_z(t/s)w(t)\,dt,\qquad
w(t)=\frac{1+\log t}{t^2\log^2t},\qquad
J_x^{\eta_z}(n)=P_x^{\eta_z}(n)-P_x^{\eta_z}(n+1).
$$

For fixed $x>1$, $z\ge2$ and a finite cutoff $Y\ge1$, the
parameter choice matching the harmonic coefficients is

$$
q=P_z,\qquad X=Y,\qquad
H_Y(t)=\frac Yt P_x^{\eta_z}(Y/t).
$$

Its finite left-hand expression is

$$
\sum_{\substack{n\le Y\\(n,P_z)=1}}\mu(n)P_x^{\eta_z}(n)
-YP_x^{\eta_z}(Y)m_{P_z}(Y).
$$

The local absolute-continuity hypothesis for $H_Y$ is checked in the
application below. Using Theorem 1.1 still requires a specified
admissible $h$ and an estimate for the actual residual

$$
H_Y'(t)-\frac1t\sum_{n\le t}\frac{(-1)^{n+1}}n h(n/t).
$$

The nonnegative $A_q$ prefix does not determine the sign of this
residual integral. Passing from the finite expression to the owning
complete pairing

$$
I_\psi(x)=\sum_{n\ge1}M_{P_z}(n)J_x^{\eta_z}(n),\qquad
M_{P_z}(n)=\sum_{\substack{r\le n\\(r,P_z)=1}}\mu(r)
$$

also requires the finite summation-by-parts endpoint, the displayed
harmonic endpoint, and all infinite-tail/interchange budgets at the
same $x,z$. The unit, original head and complementary rows cannot be
omitted. The owning §434 records actual negative $J$ windows at $x=z$;
Theorem 1.2 concerns different coefficients and supplies no positive
representation of this complete kernel.

The [existing finite Abel interface](../Analytic/sanftenberg2026harmonicabel.md)
already retains both endpoints and a directed monotone-weight budget.
Its finite identity should be reused; matching the actual coprime
kernel, controlling signed variation and accepting the infinite tail
remain separate obligations. The
[original Alladi estimate](../Analytic/alladi1982roughmobius.md)
already supplies uniform rough-prefix information, including boundary
compensation. Neither that input nor these weighted identities supplies
the remaining complete signed Robin estimate or proves RH.

## The actual logarithmic-scale curvature and centered second Abel formula

The following is a paper-level application of the existing factorial
Mellin identity in [FIB §432, SE.2–SE.3](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
and the fixed-domain decomposition in [§471, FD.1–FD.5](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_CURVATURE_APPROXIMATION.md).
Classical parameter differentiation and two integrations by parts are
reused; no new supplier theorem, priority or Lean verification is claimed.

For $x\ge e$, write $\ell=\log x$, $Q_x(s)=sP_x^\eta(s)$ and

$$
\mathcal G_{z,x}(r)=e^rP_x^{\eta_z}(e^r)
=\sum_{d\mid P_z}\frac{\mu(d)}d Q_x(de^r),\qquad
E_z(s)=\prod_{p\le z}(1-p^{-s}),\qquad C_z=E_z(1)^{-1}.
$$

This $Q_x$ is the scaled factorial kernel, not the original $R$-kernel
norm also denoted $Q_x$ in a separate source. The finite filter is shared
by every term; in particular $d=1$ remains present.

The substitution $t=sy$ in the original integral gives, for every $s>0$,

$$
Q_x(s)=\int_{x/s}^\infty\frac{\eta(y)}{y^2}
\left[\frac1{\log(sy)}+\frac1{\log^2(sy)}\right]dy.
$$

On a compact positive $s$-interval the moving lower endpoint stays away
from zero, $\log(sy)\ge\ell$, and $\eta$ is bounded on bounded
$y$-intervals. On the remaining tail, $|\eta(y)|\le1+\log y$ supplies
integrable bounds for the kernel and its scale derivative. Differences
of the moving-boundary integrals are therefore bounded by a constant
times the difference of their endpoints. Thus $Q_x$ is locally
Lipschitz, including when $x/s$ crosses an integer. Finite filtering and
smooth composition give the local absolute continuity of
$H_Y(t)=\mathcal G_{z,x}(\log(Y/t))$ required by Theorem 1.1. This
regularity pays no sign condition on the theorem's chosen-$h$ residual.

For $r\ge\ell$ the existing decomposition is
$Q_x(e^r)=F_\ell(r)+E(r)$, with
$F_\ell(r)=r\log r+c_\ell r+d_\ell-r^{-1}$ and the complete
high-domain $E$ of FD.3. Twice differentiating its fixed domain gives

$$
F_\ell''(r)=r^{-1}-2r^{-3},\qquad
E''(r)=\int_1^\infty\frac{\eta(y)}{y^2}
\left[\frac2{(r+\log y)^3}+\frac6{(r+\log y)^4}\right]dy.
$$

The same bound on $\eta$ justifies differentiation and absolute
interchange. Substituting the existing Mellin identity

$$
\int_1^\infty\eta(y)y^{-2-t}dy
=-\frac{\zeta'(1+t)}{1+t}-t^{-2}+t^{-1}\qquad(t>0)
$$

into the Laplace representations of these reciprocal powers cancels
all elementary terms, leaving the actual full curvature

$$
\boxed{\displaystyle
\mathcal G_{z,x}''(r)=\int_0^\infty e^{-rt}E_z(1+t)
[-t^2\zeta'(1+t)]\,dt>0,\qquad r\ge\ell.}
$$

Indeed the factor before filtering is
$1-t^2+(t^2+t^3)\int_1^\infty\eta(y)y^{-2-t}dy
=-t^2\zeta'(1+t)$. At zero it tends to one; at infinity it decays
exponentially times a polynomial. Finite filtering can therefore be
performed inside the absolutely convergent integral. Positivity uses
$E_z(1+t)>0$ and $-\zeta'(1+t)=\sum_{n\ge2}(\log n)n^{-1-t}>0$.
This is the curvature of the original kernel; an unrelated positive
Laplace approximant is not substituted for it. For integers $n\ge x$,
the original adjacent-row kernel still is

$$
J_x^{\eta_z}(n)=\int_n^{n+1}
\frac{\mathcal G_{z,x}(\log s)-\mathcal G_{z,x}'(\log s)}{s^2}\,ds.
$$

Thus positive second derivative does not imply a positive row kernel:
the affine part of $\mathcal G$ is absent from its second derivative
but remains in this expression and in the endpoints below.

Set, for $r\ge0$,

$$
m_z(r)=\sum_{\substack{n\le e^r\\(n,P_z)=1}}\frac{\mu(n)}n,
\qquad A_z(r)=\check m_{P_z}^{(1)}(e^r),\qquad
\varepsilon_z(r)=A_z(r)-C_z.
$$

Here $A_z'=m_z$ almost everywhere, $A_z$ is continuous and locally
absolutely continuous, and the jumps of the right-continuous $m_z$
have their original weights $\mu(n)/n$. For integers $x\le D<Y$,
put $a=\log D$, $b=\log Y$. The exact twice-integrated finite Abel
identity is

$$
\boxed{\displaystyle
\sum_{\substack{D<n\le Y\\(n,P_z)=1}}\mu(n)P_x^{\eta_z}(n)
=\left[\mathcal G_{z,x}(r)m_z(r)
-\mathcal G_{z,x}'(r)\varepsilon_z(r)\right]_a^b
+\int_a^b\varepsilon_z(r)\mathcal G_{z,x}''(r)\,dr.}
$$

First integrate $\mathcal G$ against the atomic measure $dm_z$;
then integrate $m_z=A_z'$ against $\mathcal G'$. Replacing $A_z$
by $\varepsilon_z+C_z$ cancels $C_z[\mathcal G']_a^b$ exactly.
The lower atom $n=D$ is excluded and the upper atom $n=Y$ is
included. Neither affine endpoint has been discarded.

For each fixed $x,z$, CP.3 and $m_z(r)\to0$ give $m_z(r)=O_z(r^{-3})$
by partial summation. Corollary 7.5 of the
[logarithmic-sum source](zunigaalterman2026logmobius.md) gives
$\varepsilon_z(r)=O_z(r^{-1})$. The same fixed finite-filter
FD decomposition gives $\mathcal G=O_{x,z}(r\log r)$,
$\mathcal G'=O_{x,z}(1+\log r)$ and
$\mathcal G''=E_z(1)/r+O_z(r^{-2})$. Both upper endpoints vanish,
and the last integral converges absolutely. The original finite
summation-by-parts endpoint $M_z(Y)P_x^{\eta_z}(Y+1)$ also vanishes
by CP.3. Consequently the complete pairing can be written as

$$
\begin{aligned}
I_\psi(x)={}&
\sum_{\substack{n\le D\\(n,P_z)=1}}\mu(n)P_x^{\eta_z}(n)
-\mathcal G_{z,x}(a)m_z(a)
+\mathcal G_{z,x}'(a)\varepsilon_z(a)\\
&+\int_a^\infty\varepsilon_z(r)\mathcal G_{z,x}''(r)\,dr.
\end{aligned}
$$

The finite head includes the original unit. These limit arguments are
for fixed $x,z$; their constants do not constitute a growing-primorial
estimate. The constant $C_z[\mathcal G']_a^b$ is canceled in the finite identity
before taking the infinite limit; the centered integral is not split
into two separately convergent integrals.

The missing estimate is now a common-filter estimate for the centered
error against this actual positive curvature, with the displayed head
and endpoints. Positivity of the curvature does not fix the sign of
$\varepsilon_z$. Existing complete remote-tail bounds in
[Alladi's application](../Analytic/alladi1982roughmobius.md#uniform-asymptotic-far-tails-for-a-polynomially-growing-filter)
should be reused, rather than rederived; they leave the signed head.
The final Robin consumer still includes the actual integer's pressure
loss $d_N$ in $\Delta(N)=I_\psi(\log N)+R(\log N)+d_N$ as in
[§§481, 491](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_DYADIC_RESOLVENT.md).
No sign for that complete quantity or proof of RH follows here.
