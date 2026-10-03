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
