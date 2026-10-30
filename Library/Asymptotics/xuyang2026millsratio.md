---
bibkey: xuyang2026millsratio
authors: Hui-Zuo Xu and Zhen-Hang Yang
year: 2026
title: Higher order monotonicity involving the Mills ratio with applications
doi: 10.1186/s13660-026-03505-9
url: https://doi.org/10.1186/s13660-026-03505-9
claim: "Conjecture 7.1 proposes complete monotonicity of the signed asymptotic remainders of Y at a = -1."
strata_touched:
  - D5/S3/Analytic/XuYangMillsRemainder/Result
license: citation-only
triage: anchor
---

# Mills-ratio asymptotic remainders

## Verified locator

https://doi.org/10.1186/s13660-026-03505-9

Journal of Inequalities and Applications (2026) 2026:98.
The locators below are printed article pages.

## Source statements

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

## Mathematical correspondence

`millsRatio` uses the displayed Gaussian-tail normalization of $R$.
`Y` is the defining expression in (1.8), and `u` retains the Gamma factors
and finite sum of (3.7). `D` is the remainder in Conjecture 7.1.
`CompletelyMonotoneOn` means $C^\infty$ on $(0,\infty)$ together with
$(-1)^m f^{(m)}(x)\ge0$ for every nonnegative integer $m$ and every $x>0$.
`claim` quantifies over all integers $n\ge2$.

At $(a,b)=(-1,-3)$, the source coefficients satisfy $u_1=u_2=0$.
Theorem 4.2, printed p. 14, treats $n=2,3,4$; the all-index assertion
extends those cases. Since $D_1=D_2$, the signed remainder at $n=1$ is
$-D_2$ and is excluded. The question for general $a$ is separate.
