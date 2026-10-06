---
bibkey: romik2021orthogonal
authors: Dan Romik
year: 2021
title: Orthogonal polynomial expansions for the Riemann xi function in the Hermite, Meixner–Pollaczek, and continuous Hahn bases
doi: null
url: https://doi.org/10.4064/aa200515-10-3
claim: Equations (1.6)–(1.11) define the original theta differential weight and its logarithmic kernel and give the Mellin and all-complex Fourier representations of the Riemann xi function.
strata_touched:
  - D5/S3/Analytic/Fourier/ThetaDifferentialKernel
  - D5/S3/Analytic/Fourier/XiThetaTransform
license: citation-only
triage: anchor
---

# The original theta kernel and xi

On page 2 of the Online First text, equations (1.6)–(1.9) use
`theta(t) = 1 + 2 sum(n>=1) exp(-pi*n^2*t)`,
`omega(t) = sum(n>=1) (2*pi^2*n^4*t^2 - 3*pi*n^2*t)*exp(-pi*n^2*t)`,
and `Phi(x) = 2*exp(x/2)*omega(exp(2*x))`.
Equation (1.9) explicitly states `Phi(-x) = Phi(x)` for every real x.
No absolute value occurs in the definition (1.8). Equation (1.6) also gives
the positive-index theta-tail identity; separating the two summable weights
in (1.7) gives the weighted-series formula used in the repository.

Page 1, equation (1.3), defines `Xi(z) = xi(1/2 + i*z)` for `z in C`.
Page 3, equations (1.10) and (1.11), states the Mellin representation of xi and
`Xi(z) = integral_R Phi(x)*exp(i*z*x) dx`, using that all-complex convention,
without an additional prefactor. These are published statements; their new
Lean proofs do not change their literature provenance. The repository derives the differential identity
`Phi = psi'' - psi/4`, where `psi(x)=exp(x/2)*(theta(exp(2*x))-1)/2`, and
identifies this original Phi with its fixed even theta kernel. These are
repository object identifications, not claims that the paper uses repository
names or the repository's absolute-value definition.

The paper also treats the physicists' Hermite, Meixner–Pollaczek and continuous
Hahn expansions. Their coefficient integrals, polynomial normalizations and
compact convergence estimates are separate obligations; the theta transform
alone does not establish those expansions or Cardon's equivalence involving
simple zeros and its specific measure and orthogonal polynomials.

## Reusable theta tail and its local scale

Lemma 2.3, printed p.10, equations (2.8)–(2.9), directly supplies

$$
\Phi(r)=O\!\left(e^{9r/2-\pi e^{2r}}\right),
$$

$$
\Phi(r)-2(2\pi^2e^{9r/2}-3\pi e^{5r/2})e^{-\pi e^{2r}}
=O\!\left(e^{9r/2-4\pi e^{2r}}\right)
\qquad(r\to+\infty).
$$

Thus, with $g(r)=e^{9r/2-\pi e^{2r}}$, positivity and continuity on the
remaining compact interval give $cg(r)\le\Phi(r)\le Cg(r)$ for $r\ge1$.
For $\delta_R=e^{-2R}$ the identity

$$
\log\frac{g(R+s)}{g(R)}
=\frac92s-\pi e^{2R}(e^{2s}-1)
$$

gives $\Phi(R+s)\asymp\Phi(R)$ uniformly for
$-\delta_R\le s\le2\delta_R$. This is comparison by constants,
not a ratio tending to one.

A derivative estimate must use the normally convergent original series
(1.8), rather than differentiate the displayed remainder. Its differentiated
summands are bounded by $Ce^{13r/2}n^6e^{-\pi n^2e^{2r}}$ for $r\ge1$.
The uniformly summable series after removing its first exponential gives
$|\Phi'(r)|\le Ce^{2r}g(r)$, hence
$|\Phi'(r)/\Phi(r)|\le Ce^{2r}$.
These are paper-level applications of the source series and Lemma 2.3,
used by the [Gamma tail and same-test compensation estimates](../Weil/chenwang2012weighted.md).
They are not additional tail theorems attributed to Romik or new Lean proofs.

## Explicit original-series majorants

The normally convergent source series also supplies coarse constants for
the [prime-diagonal error transfer](../Weil/trudgian2014pnt.md) and the
[full mixed-operator cutoff estimates](../Weil/lenz2010compactness.md).
These are analytic upper bounds, not fitted numerical values or new
theta representation theorems.

For $x\ge0$, put $u=e^{2x}\ge1$ and $v_n=\pi n^2u$. Differentiating
the original series gives

$$
\begin{aligned}
\Phi(x)&=2u^{1/4}\sum_{n\ge1}(2v_n^2-3v_n)e^{-v_n},\\
\Phi'(x)&=u^{1/4}\sum_{n\ge1}
             (-8v_n^3+30v_n^2-15v_n)e^{-v_n}.
\end{aligned} \tag{TS}
$$

For $H=\Phi/2+|\Phi'|$, positivity of $\Phi$ and the triangle inequality
therefore give

$$
H(x)\le u^{1/4}\sum_{n\ge1}
                   (8v_n^3+32v_n^2+15v_n)e^{-v_n}. \tag{HM}
$$

Use $u^{1/4}\le u=v_n/(\pi n^2)$, $\pi>3$,
$\sum_{n\ge1}n^{-2}\le2$, and the standard maximum
$v^ke^{-v}\le k^ke^{-k}$. The elementary lower bounds
$e^4>54$, $e^3>20$ and $e^2>7$ yield

$$
\begin{aligned}
\|\Phi\|_\infty&\le\frac83\frac{27}{e^3}<\frac{18}{5},\\
H_\infty&\le\frac23\left(
             \frac{1024}{27}+\frac{216}{5}+\frac{60}{7}\right)<60.
\end{aligned} \tag{SC}
$$

Evenness extends these bounds to the whole real line. For the weighted
integral, use evenness of $H$, $\cosh(x/2)\le e^{x/2}$ for $x\ge0$,
and $u^{1/2}\le u$. Substitution $dx=du/(2u)$ gives

$$
\begin{aligned}
M_H:=\int H(x)e^{x/2}\,dx
&=2\int_0^\infty H(x)\cosh(x/2)\,dx\\
&\le\sum_{n\ge1}\frac1{\pi n^2}
           \int_0^\infty(8v^3+32v^2+15v)e^{-v}\,dv\\
&\le\frac{254}{3}<85.
\end{aligned} \tag{MC}
$$

The polynomial integral is $8\cdot6+32\cdot2+15=127$.
Its extension from $v\ge\pi n^2$ to $v\ge0$ only increases the bound.

For a spatial tail majorant, split the exponential in (TS) and use
$v^3e^{-v/2}\le216e^{-3}<216/20$. Since $v_n\ge3u$,

$$
\Phi(x)\le\frac{144}{5}\exp\left(-\frac32e^{2|x|}\right). \tag{ST}
$$

Consequently, for $r\ge0$,

$$
T(r):=\int_{|x|>r}\Phi(x)\,dx
\le\frac{96}{5}e^{-2r}\exp\left(-\frac32e^{2r}\right). \tag{IT}
$$

Indeed, the substitution $u=e^{2x}$ on each even tail gives
$(144/5)\int_{e^{2r}}^\infty e^{-3u/2}\,du/u$;
bound $1/u$ by $e^{-2r}$ and integrate the remaining exponential.
All constants are deliberately loose and keep the original kernel and
normalization. These model applications have no new Lean certification
or originality claim.

## Weighted Fourier coefficient suppliers

For the [weighted Fourier cutoff](../Weil/fukushima2011dirichlet.md), define
on the whole real line

$$
s(x)=\sqrt{\frac{\Phi(x)}{2\cosh(x/2)}}.
$$

The existing strictly positive smooth even original kernel makes $s$
smooth and even, including at zero. The following original-series
estimates supply $s\in H^3(\mathbb R)$, bounded $s,s'$, and the derivative
summability of the complete prime graph. They are model deductions from
the source series, with no useful numerical constant sizes or new Lean
certification asserted.

For $x\ge0$, $u=e^{2x}\ge1$, write

$$
\Phi(x)=\sum_{n\ge1}
 (4\pi^2n^4e^{9x/2}-6\pi n^2e^{5x/2})e^{-\pi n^2u}.
$$

Every summand is positive. Its first summand gives
$\Phi(x)>18e^{5x/2}e^{-\pi u}$, using $\pi>3$.
Define derivative polynomials by

$$
P_{0,a}(z)=1,\qquad
P_{j+1,a}(z)=(a-2z)P_{j,a}(z)+2zP'_{j,a}(z),\qquad
P_{j,a}(z)=\sum_{k=0}^jp_{j,a,k}z^k.
$$

Direct differentiation gives
$\partial_x^j(e^{ax}e^{-\pi n^2u})
=e^{ax}e^{-\pi n^2u}P_{j,a}(\pi n^2u)$.
For $0\le j\le3$ let

$$
C_j=\sum_{n\ge1}e^{-\pi(n^2-1)}
\left(4\pi^2n^4\sum_{k=0}^j|p_{j,9/2,k}|\pi^kn^{2k}
 +6\pi n^2\sum_{k=0}^j|p_{j,5/2,k}|\pi^kn^{2k}\right).
$$

Normal convergence of the original series permits termwise
differentiation. Using $u^k\le u^j$ and
$e^{-\pi(n^2-1)u}\le e^{-\pi(n^2-1)}$ gives

$$
|\Phi^{(j)}(x)|\le C_je^{(9/2+2j)x}e^{-\pi u},\qquad
\frac{|\Phi^{(j)}(x)|}{\Phi(x)}
\le\gamma_je^{(2+2j)x},\quad\gamma_j=C_j/18. \tag{WC1}
$$

These constants have explicit tail majorants. For $q\le10$, $n\ge2$,
the ratio of successive terms $a_n=n^qe^{-\pi(n^2-1)}$ is at most
$r_*=(3/2)^{10}e^{-5\pi}<1$. Every monomial in $C_j$ has degree at
most ten, so its tail after $N\ge1$ is at most
$a_{N+1}/(1-r_*)$, with its displayed coefficient retained.

Put $d=2\cosh(x/2)$ and $\ell=\log s$. The first three derivatives of
$\log d$ have absolute bounds $1/2,1/4,1/4$. Thus

$$
|\ell'|\le A_1e^{4x},\quad |\ell''|\le A_2e^{8x},\quad
|\ell'''|\le A_3e^{12x},
$$

where

$$
\begin{aligned}
A_1&=\gamma_1/2+1/4,\\
A_2&=(\gamma_2+\gamma_1^2)/2+1/8,\\
A_3&=(\gamma_3+3\gamma_1\gamma_2+2\gamma_1^3)/2+1/8.
\end{aligned}
$$

Since $d\ge e^{x/2}$, (WC1) gives
$s\le\sqrt{C_0}\,u e^{-\pi u/2}$. Apply
$s'=s\ell'$, $s''=s((\ell')^2+\ell'')$, and
$s'''=s((\ell')^3+3\ell'\ell''+\ell''')$ to obtain

$$
|s^{(j)}(x)|\le\sqrt{C_0}B_ju^{1+2j}e^{-\pi u/2},\qquad
(B_0,B_1,B_2,B_3)=(1,A_1,A_1^2+A_2,A_1^3+3A_1A_2+A_3).
$$

For $c=3/8$, $\zeta=\pi/2-c>0$, define
$v_m=\max\{1,m/\zeta\}$, $M_m=v_m^me^{-\zeta v_m}$ and
$K_j=\sqrt{C_0}B_jM_{1+2j}$. Maximizing the remaining scalar factor,
and then using evenness, yields

$$
|s^{(j)}(x)|\le K_je^{-c e^{2|x|}}
\qquad(x\in\mathbb R,\ 0\le j\le3). \tag{WC2}
$$

Substitution on the two tails gives, with the unitary Fourier convention,

$$
\begin{aligned}
\|s^{(j)}\|_2^2&\le K_j^2\frac{e^{-2c}}{2c},\\
\|s\|_{H^3}^2
:=\int(1+\xi^2)^3|\widehat s(\xi)|^2d\xi
&\le\frac{e^{-2c}}{2c}\sum_{j=0}^3\binom3jK_j^2,\\
\|(s^2)'\|_\infty&\le2K_0K_1.
\end{aligned} \tag{WC3}
$$

For the prime operator use the same coefficients as in the mixed model:
$t_n=\log n$, $w_n=\Lambda(n)/\sqrt n$ and
$b_n(x)=w_ns(x)s(x+t_n)$. Product differentiation and
$e^{2|x|}+e^{2|x+t_n|}\ge2n$ imply
$\|b_n'\|_\infty\le2K_0K_1w_ne^{-2cn}$.
With $r=e^{-2c}$ and $w_n\le n$,

$$
\sum_{n\ge2}\|b_n'\|_\infty
\le2K_0K_1\left(\frac r{(1-r)^2}-r\right)<\infty. \tag{WC4}
$$

This sum is per representative undirected edge and includes every prime
power. The translated adjoint has the same derivative supremum norm, so
the explicitly two-direction estimate is

$$
\sum_{n\ge2}\left(\|b_n'\|_\infty+
 \|(b_n(\cdot-\log n))'\|_\infty\right)
\le4K_0K_1\left(\frac r{(1-r)^2}-r\right). \tag{WC5}
$$

These estimates discharge the coefficient hypotheses in (WF2), (WF5)
and (WF7) of the linked cutoff construction for the actual theta model.
They retain the full graph and provide deliberately coarse constants;
useful bandwidth and matrix certificates require further quantitative
work.

## Source anomalies retained

On page 40 the printed c-prime integral omits the factor `2*sqrt(2)` used in the
original c coefficients, while asserting equality of the even coefficients.
The Pollaczek prose says orthonormal, whereas equation (A.12) gives a nonunit
norm. Neither discrepancy is silently repaired or used as an equality here.
The separate Cardon source's odd-extension/jump and recurrence/tail issues
remain separate from Romik's theta formulas.

## Verified locator

- URL: https://doi.org/10.4064/aa200515-10-3
- DOI: 10.4064/aa200515-10-3

The author-hosted Online First PDF was retrieved on 2026-09-11 from
https://www.math.ucdavis.edu/~romik/data/uploads/papers/riemannxi-acta-online-first.pdf.
Its SHA-256 is `a28edcf341776bf801e9d0c2de4631639b2c46c579a67a38cc2788d255e2ae87`.
The page references above use that 72-page PDF's internal pagination; they are
not converted to the final Acta Arithmetica 200(3), 259–329 pagination.
