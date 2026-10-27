---
bibkey: ramarezuniga2026identityfactory
authors: Olivier Ramaré and Sebastian Zuniga-Alterman
year: 2026
title: "Möbius function and primes: an identity factory with applications"
doi: 10.1090/mcom/4216
url: https://arxiv.org/abs/2312.05138v3
claim: "Theorems 1.1–1.2 supply a finite weighted identity and uniform coprime logarithmic Möbius positivity; the actual filtered Robin kernel has a positive logarithmic-scale curvature, an exact centered second-Abel and real-axis application, and a compensated prime-resolution transfer; the complete Robin lower bound remains open."
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

## A complete centered pairing with the positive curvature extension

This application reuses the preceding actual-curvature formula and the
same finite-filter centered error. It does not assert a new Laplace
transform theorem or literature priority. Define, now on the whole
nonnegative half-line,

$$
k_z(r)=\int_0^\infty e^{-rt}E_z(1+t)
[-t^2\zeta'(1+t)]\,dt,\qquad r\ge0.
$$

It agrees with $\mathcal G_{z,x}''$ for $r\ge\log x$. Below that
threshold it is an auxiliary extension, not an assertion about the
actual low-domain second derivative. The density is positive, tends
to $E_z(1)$ at zero, and is $O(t^2 2^{-t})$ at infinity. Thus $k_z$
is finite and continuous at zero, positive everywhere, and
$k_z(r)\sim E_z(1)/r$ as $r\to\infty$ for each fixed filter.

Absolute Dirichlet integration gives, for every $t>0$,

$$
\int_0^\infty e^{-tr}\varepsilon_z(r)\,dr
=\frac1{t^2\zeta(1+t)E_z(1+t)}-\frac{C_z}{t}<0.
$$

Indeed integrating each $(r-\log n)_+$ contributes
$n^{-t}/t^2$, and $\sum |\mu(n)|n^{-1-t}$ is finite. The strict
sign uses only the classical integral comparison
$t\zeta(1+t)>1$ and $E_z(1+t)\ge E_z(1)=1/C_z$.
It is a sign of the transform, not pointwise nonpositivity of
$\varepsilon_z$.

Corollary 7.5 gives $\varepsilon_z(r)=O_z(r^{-1})$ for fixed $z$.
Together with local boundedness and the displayed curvature bounds,
this pays $\int_0^\infty|\varepsilon_z(r)|k_z(r)dr<\infty$.
Tonelli for the absolute integrand, followed by Fubini, therefore gives

$$
\boxed{\displaystyle
\mathcal H_z:=\int_0^\infty\varepsilon_z(r)k_z(r)\,dr
=\int_0^\infty[-\zeta'(1+t)]
\left[\frac1{\zeta(1+t)}-C_ztE_z(1+t)\right]dt<0.}
$$

The cancellation takes place inside one integrand. With
$S_z=\sum_{p\le z}\log p/(p-1)$, its limit at zero is
$-(\gamma+S_z)$: use
$\zeta(1+t)^{-1}=t-\gamma t^2+O(t^3)$ and
$E_z(1+t)=E_z(1)(1+S_zt+O_z(t^2))$.
At infinity it is $O_z((1+t)2^{-t})$. The individual pieces in
square brackets cannot be integrated separately at zero.

This determines a full signed pairing without discarding the common
Euler factor. It does not determine the original Robin pairing:
that consumer starts at $a\ge\log x$, retains the finite unit/head and
both affine endpoints, and must subtract the whole interval $[0,a]$
from $\mathcal H_z$. A sign for the auxiliary full half-line is not a
sign for that truncated quantity.

## Exact real-axis payment of the truncated centered tail

Keep an integer $D\ge x\ge e$ and write $a=\log D$. All arithmetic
objects use the same actual filter. Put

$$
U_{z,D}(t)=\sum_{\substack{n\le D\\(n,P_z)=1}}
\frac{\mu(n)}{n^{1+t}},\qquad
m=m_z(a),\quad \epsilon=\varepsilon_z(a),
$$

$$
\mathcal B_{z,D}(t)=\frac1{\zeta(1+t)}
-E_z(1+t)U_{z,D}(t)
+E_z(1+t)e^{-at}(m+t\epsilon).
$$

Then the entire tail has the exact expression

$$
\boxed{\displaystyle
\mathcal T_{z,D}:=\int_a^\infty\varepsilon_z(r)k_z(r)\,dr
=\int_0^\infty[-\zeta'(1+t)]\mathcal B_{z,D}(t)\,dt.}
$$

To see the finite-head compensation, integrate the original ramps
before applying the positive mixture:

$$
\int_a^\infty e^{-tr}\varepsilon_z(r)dr
=\frac{[\zeta(1+t)E_z(1+t)]^{-1}-U_{z,D}(t)}{t^2}
+e^{-at}\left(\frac m{t^2}+\frac\epsilon t\right).
$$

Atoms $n\le D$ give the last two terms; atoms $n>D$ give the
Dirichlet-series remainder. This includes the atom at $D$ in the
finite prefix, consistently with the existing right-continuous Abel
convention. Multiplication by $E_z(1+t)[-t^2\zeta'(1+t)]$ gives the
boxed identity. The same fixed-filter absolute budget as above pays
the interchange. In particular this is an exact identity for every
finite $z,D$, not a limit obtained by treating fixed-filter constants
as uniform in a growing primorial.

Both cancellations at $t=0$ can be read from finite moments. Let

$$
A_{z,D}^{(2)}=\sum_{\substack{n\le D\\(n,P_z)=1}}
\frac{\mu(n)}n(a-\log n)^2.
$$

The constant and linear Taylor coefficients of $\mathcal B_{z,D}$
vanish, and the complete integrand has the finite limit

$$
\lim_{t\downarrow0}[-\zeta'(1+t)]\mathcal B_{z,D}(t)
=a-\gamma-S_z-\frac{A_{z,D}^{(2)}}{2C_z}.
$$

Indeed
$e^{-at}(m+t\epsilon)-U_{z,D}(t)
=-C_zt+(aC_z-A_{z,D}^{(2)}/2)t^2+O_{z,D}(t^3)$.
At infinity the full integrand is $O_{z,D}((1+t)2^{-t})$.
These statements establish ordinary absolute convergence of the
combined real-axis integral. Its separate terms would each have
nonintegrable zero-end pieces.

The original complete consumer is therefore

$$
\boxed{\begin{aligned}
I_\psi(x)={}&\sum_{\substack{n\le D\\(n,P_z)=1}}
\mu(n)P_x^{\eta_z}(n)
-\mathcal G_{z,x}(a)m
+\mathcal G_{z,x}'(a)\epsilon
+\mathcal T_{z,D}.
\end{aligned}}
$$

This consumes the earlier twice-Abel identity without dropping its
finite unit, its lower-cut atom convention or either affine endpoint.
It replaces an infinite centered Möbius tail by one explicit real-axis
integral and finite prefix data. No growing-modulus pointwise error
factor is substituted for that signed integral.

For $D\le z$, the prefix is just the unit, so $m=1$,
$\epsilon=a-C_z$ and $U_{z,D}=1$. More generally, the existing
unit-and-prime range $D\le z^2$ gives

$$
\begin{aligned}
U_{z,D}(t)&=1-\sum_{z<p\le D}p^{-1-t},\\
m&=1-\sum_{z<p\le D}p^{-1},\\
\epsilon&=a-C_z-\sum_{z<p\le D}\frac{\log(D/p)}p,\\
\sum_{\substack{n\le D\\(n,P_z)=1}}\mu(n)P_x^{\eta_z}(n)
&=P_x^{\eta_z}(1)-\sum_{z<p\le D}P_x^{\eta_z}(p).
\end{aligned}
$$

These are the same actual unit-and-prime inputs already used in
[Alladi's application](../Analytic/alladi1982roughmobius.md);
they are not a new rough-number estimate. At $D=\lceil x\rceil\le z^2$
the finite data use only the unit and primes between $z$ and that
source cutoff. This is an exact representation, not a computational
cost or numerical-certification claim: the original factorial kernels
and the combined real-axis integral still have to be evaluated or
bounded.

For an actual integer $N$ and its chosen common filter, set $x=\log N$
and use the same $D\ge x$. The remaining sufficient target is a lower
bound on the entire displayed expression that beats
$-R(\log N)-d_N$. The sign $\mathcal H_z<0$ supplies no such lower
bound: the subtracted low interval, the head and the endpoints must
be combined. The original same-integer loss $d_N$, all low rows and
the signed real-axis bracket remain present. No Robin-safe integer
range, global Robin sign, RH proof or Lean verification is claimed.

## A prime-resolution change transfers the signed account exactly

There is also a precise cost for refining this prime section. Let $p$
be the next prime after the prefix $P_z$, and write $P_{z'}=pP_z$.
The elementary finite-product relation is

$$
C_{z'}E_{z'}(1+t)=C_zE_z(1+t)
\left(1+\frac{1-p^{-t}}{p-1}\right).
$$

Consequently the full centered pair satisfies

$$
\boxed{\displaystyle
\mathcal H_{z'}-\mathcal H_z=-\delta_{z,p}<0,\qquad
\delta_{z,p}=\frac1{p-1}\int_0^\infty
t[-\zeta'(1+t)]C_zE_z(1+t)(1-p^{-t})\,dt>0.}
$$

Including the prefactor $1/(p-1)$, the integrand has finite limit
$\log p/(p-1)$ at zero and an exponentially decaying tail. Thus this difference is an ordinary
convergent positive integral, not a subtraction of divergent budgets.

For the same $x,D$ define the explicit complementary account

$$
\begin{aligned}
\mathcal L_{x,z,D}={}&
\sum_{\substack{n\le D\\(n,P_z)=1}}\mu(n)P_x^{\eta_z}(n)
-\mathcal G_{z,x}(a)m_z(a)
+\mathcal G_{z,x}'(a)\varepsilon_z(a)\\
&-\int_0^a\varepsilon_z(r)k_z(r)dr.
\end{aligned}
$$

The last integral uses only finite prefix data up to $D$; its curvature
below $\log x$ is the declared auxiliary extension. The complete
same-source identity now reads

$$
I_\psi(x)=\mathcal H_z+\mathcal L_{x,z,D}.
$$

The already established filter invariance of $I_\psi$ in CP.2 then
forces the exact companion transfer

$$
\boxed{\displaystyle
\mathcal L_{x,z',D}-\mathcal L_{x,z,D}=\delta_{z,p}.}
$$

Thus every added prime makes the auxiliary full pair strictly more
negative and raises the complementary account by exactly the same
amount. Prime-section refinement redistributes the original response;
it does not create an extra Robin reserve. A FIB candidate can use this
section only with the same actual integer, $x=\log N$, its certified
prime data and its original loss $d_N$. Neither a recursive address nor
this conservation identity supplies the still missing one-sided bound
for their complete sum.
