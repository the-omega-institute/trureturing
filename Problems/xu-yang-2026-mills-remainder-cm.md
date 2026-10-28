---
slug: xu-yang-2026-mills-remainder-cm
bibkey: xuyang2026millsratio
doi: 10.1186/s13660-026-03505-9
triage: theorem
motivation_gids:
  - D5/S3/Analytic/XuYangMillsRemainder/Result.result
url: https://doi.org/10.1186/s13660-026-03505-9
---

# Complete monotonicity of the Xu–Yang Mills remainders

## Problem

H.-Z. Xu and Z.-H. Yang, *Higher order monotonicity involving the Mills
ratio with applications*, Journal of Inequalities and Applications
2026:98, DOI 10.1186/s13660-026-03505-9.

Mills-ratio definition, printed p. 2:

> The Mills ratio [3] is defined by
>
> $$R\equiv R(x)=\frac{1-\Phi(x)}{\phi(x)}
> =e^{x^2/2}\int_x^\infty e^{-t^2/2}\,dt,\quad x\ge0,$$
>
> which satisfies the differential equation of first order:
>
> $$R'=xR-1.\qquad(1.1)$$

Here $\phi(x)=e^{-x^2/2}/\sqrt{2\pi}$ and
$\Phi(x)=\int_{-\infty}^x\phi(t)\,dt$ are the standard Gaussian density and
cumulative distribution function used in the preceding source sentences.

The bound family in (1.5), printed p. 2, is

$$\varphi_{p,q,r}(x)=\frac{p}{\sqrt{x^2+q}+rx},
\qquad p,q>0,\quad r\ge0.$$

Equation (1.8), printed p. 3, with its complete surrounding statement:

> Note that all bounds of the form $\varphi_{p,q,r}(x)$ can be derived from the inequality
>
> $$Y_{a,b}(x):=(x^2+a)R^2(x)+bxR(x)<(>)c\qquad(1.8)$$
>
> for all $x>0$, $a,b\in\mathbb R$, where
>
> $$c=\lim_{x\to0}Y_{a,b}(x)=\frac{a\pi}{2}
> \quad\text{or}\quad c=\lim_{x\to\infty}Y_{a,b}(x)=b+1.$$

Equation (3.7), printed p. 6, gives the coefficients following the asymptotic
expansion in Theorem 3.1:

> where
>
> $$u_n\equiv u_n(a,b)=(b+1)\frac{2^n\Gamma(n+1/2)}{\Gamma(1/2)}
> +(n-a)(n-1)!\sum_{k=0}^{n-1}
> \frac{2^k\Gamma(k+1/2)}{\Gamma(1/2)k!}.\qquad(3.7)$$
>
> In particular, $u_1=b+2-a$, $u_2=3b+7-2a$, $u_3=15b+36-7a$, and $u_4=105b-36a+249$.

Conjecture 7.1, printed p. 27, complete statement:

> Moreover, inspired by Theorem 4.2, we propose the following conjecture.
>
> Conjecture 7.1 Let
>
> $$D_n(x,a)=Y_{a,a-2}(x)-\left(a-1+\sum_{k=1}^{n}
> \frac{(-1)^ku_k}{x^{2k}}\right),$$
>
> where $u_k$ is defined by (3.7). Then $x\mapsto(-1)^nD_n(x,-1)$ is CM on $(0,\infty)$.


### Formal reading

The namespace is `D5.S3.Analytic.XuYangMillsRemainder.Result`.
The definitions `millsRatio`, `Y`, `u` and `D` retain the displayed
Gaussian integral, polynomial expression, Gamma coefficients and finite
remainder. Here $\Gamma$ is Euler's Gamma function, $k!$ is the factorial of the
nonnegative integer $k$, and all integrals use Lebesgue measure.
`CompletelyMonotoneOn f` means $f$ is $C^\infty$ on $(0,\infty)$
and every signed derivative $(-1)^m f^{(m)}(x)$ is nonnegative there.
`claim` quantifies over every integer $n\ge2$; `result` states `claim`.
The source does not display a lower bound for $n$ in Conjecture 7.1.
The restriction $n\ge2$ is necessary: $n=1$ fails, as explained in Triage.

## Motivation

The declaration `D5/S3/Analytic/XuYangMillsRemainder/Result.result`
settles the all-index assertion for $n\ge2$. The source note is
`D5/L/Asymptotics/xuyang2026millsratio`.
Theorem 4.2 already treats $n=2,3,4$; the additional range is $n\ge5$.

## Gap

An asymptotic expansion alone does not control a remainder for every
positive $x$, nor its derivatives of every order. A positive Laplace
representation supplies both the global sign and all derivative signs.
The Gamma coefficients must agree exactly with the coefficients removed
from that representation.

## Route

Write $h(t)=\exp(-t^2/2)$ and let
$Q(t)=\int_0^t h(s)h(t-s)\,ds$, the convolution on
the positive half-line. For $x>0$,

$$R(x)=\int_0^\infty e^{-xt}h(t)\,dt,\qquad
 R(x)^2=\int_0^\infty e^{-xt}Q(t)\,dt,$$

$$Q(t)=t\int_0^1 e^{-(1+v^2)t^2/4}\,dv.$$

Two integrations by parts, and the fundamental theorem applied to
$v\exp(-(1+v^2)t^2/4)$ and $v(1-v^2)\exp(-(1+v^2)t^2/4)$, give

$$H(x):=(x^2-1)R(x)^2-3xR(x)+2
 =\int_0^\infty e^{-xt}K(t)\,dt,$$

$$K(t)=\frac{t^5}{8}\int_0^1v^2(1-v^2)e^{-(1+v^2)t^2/4}\,dv.$$

For nonnegative integer $j$, put

$$I_j=\int_0^1(1+v^2)^j\,dv,\quad
 J_j=\int_0^1v^2(1-v^2)(1+v^2)^j\,dv,\quad
 A_j=\frac{(2j+5)!}{8\,4^j j!}J_j.$$

The recurrence $(2j+3)I_{j+1}-2(j+1)I_j=2^{j+1}$, obtained by
integrating the derivative of $v(1+v^2)^{j+1}$, identifies the original
Gamma coefficient as $u_{j+3}(-1,-3)=-A_j$. Also $u_1=u_2=0$.
Thus $H=D_2(\cdot,-1)$.

For nonnegative integer $r$ and $v\ge0$, define the finite exponential remainder

$$E_r(v)=(-1)^r\left(e^{-v}-\sum_{j=0}^{r-1}\frac{(-v)^j}{j!}\right).$$

The sum is empty when $r=0$, so $E_0(v)=\exp(-v)$. Taylor's theorem gives
$0\le E_r(v)\le v^r/r!$ and the exact recursion
$E_{r+1}(v)=v^r/r!-E_r(v)$. Set

$$K_r(t)=\frac{t^5}{8}\int_0^1v^2(1-v^2)
 E_r((1+v^2)t^2/4)\,dv.$$

For $t\ge0$, $0\le K_r(t)\le t^{2r+5}$. Integrating the finite recursion, using
$\int_0^\infty t^m\exp(-xt)\,dt=m!/x^{m+1}$, identifies

$$(-1)^rD_{r+2}(x,-1)=\int_0^\infty e^{-xt}K_r(t)\,dt.$$

Every polynomially weighted moment is integrable for $x>0$. On a
neighborhood of $x$ it is dominated using $\exp(-xt/2)$. Differentiation
under the integral yields

$$(-1)^m\frac{d^m}{dx^m}\int_0^\infty e^{-xt}K_r(t)\,dt
 =\int_0^\infty t^m e^{-xt}K_r(t)\,dt\ge0.$$

All orders of differentiability follow from the same domination.
Since $(-1)^{r+2}=(-1)^r$, this is the requested complete monotonicity.

## Falsifier

A discrepancy in the Gaussian normalization, the coefficient identity,
the finite remainder recursion or differentiation under the integral
would invalidate the connection to the original conjecture. A finite
numerical sign check alone would not establish the all-index assertion.

## Evidence

**PROVED.** `D5.S3.Analytic.XuYangMillsRemainder.Result.result` states
`claim` without additional assumptions: complete monotonicity for every
integer $n\ge2$ and every positive argument, with all derivative orders.

The experiment is published in
[the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/f43cf5dddaca195663d4e6e14153ed1512618acb/experiments/xu-yang-mills-remainder-cm).

- **COMPUTED.** Script `xu-yang-c71.py`,
  `python3 xu-yang-c71.py`, exit code 0; SHA-256
  `bdb10be43e6f8eb65b15cce53567ab6b21b82f720208d22b8f6b9392f93a6c3b`.
  The tested scope is $n\le6$, $m\le4$ and $x\in\{0.3,0.7,1,2,4,8,15\}$, at 60 decimal
  digits. The values $u_1,\ldots,u_6$ at $(-1,-3)$ are $0,0,-2,-30,-396,-5460$.
  The tested signs are positive for $n=0$ and $n=2,\ldots,6$; $n=1$ fails.
  The minimum observed margins for $n=2,\ldots,6$ are approximately
  $8.865\times10^{-9}$, $1.623\times10^{-9}$, $2.084\times10^{-10}$, $2.440\times10^{-11}$ and $2.395\times10^{-12}$.

The supplied literature check covered the Semantic Scholar citation list,
web searches of the title and DOI, and comparison with Salazar,
arXiv:2606.31647, and Yang, arXiv:2507.10954. No settlement was found in
that scope. No new network search is asserted.

## Triage

### What the settlement shows

The mechanism is positivity of a whole family of exact Laplace kernels.
The finite Taylor recursion preserves positivity after every truncation;
it supplies uniform statements in $n$ and derivative order, rather than
finite numerical evidence.
The delivered theorem asserts the paper's CM condition (signed derivatives $\ge0$);
the strict positivity mentioned in the preregistration is not asserted by the Lean theorem.

- **PROVED.** `D5.S3.Analytic.XuYangMillsRemainder.Result.result` covers
  every $n\ge2$; the range beyond Theorem 4.2 is $n\ge5$.
- **PROVED in prose.** The lower index $n=1$ fails. The original formula
  (3.7) gives $u_1(-1,-3)=u_2(-1,-3)=0$, hence $D_1=D_2$. Theorem 4.2(i),
  printed p.14, states that $-D_2(\cdot,a)$ is CM exactly when $a\ge-3/4$.
  At $a=-1$ this condition fails, so $-D_1(\cdot,-1)$ is not CM.
- **PROVED in the source.** The $n=2,3,4$ cases overlap Theorem 4.2(i)–(iii),
  printed p.14. At $a=-1$ its respective conditions $a\le-1$,
  $a\le-3/4$ and $a\le-13/23$ all hold.
- **COMPUTED.** The finite margins and their complete tested scope are
  given in Evidence; they assert no continuous-domain bound.
- **OPEN.** The analogous classification for general $a$ is not settled.
  No assertion outside $n\ge2$, $a=-1$ follows from the stated conclusion.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage, Google Scholar, citation-index completeness
and priority are unverified. Finite precision
computations do not establish uniform signs or complete monotonicity.
