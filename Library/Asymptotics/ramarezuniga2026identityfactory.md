---
bibkey: ramarezuniga2026identityfactory
authors: Olivier Ramaré and Sebastian Zuniga-Alterman
year: 2026
title: "Möbius function and primes: an identity factory with applications"
doi: 10.1090/mcom/4216
url: https://arxiv.org/abs/2312.05138v3
claim: "Theorems 1.1–1.2 supply a finite weighted identity and uniform coprime logarithmic Möbius positivity; their application to the complete filtered Robin kernel still requires regularity, signed residual and endpoint estimates."
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

This records the substitution only. Using Theorem 1.1 requires its
local absolute-continuity hypothesis for $H_Y$, a specified admissible
$h$, and an estimate for the actual residual

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
