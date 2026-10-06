---
bibkey: pintz2026mobiusoscillation
authors: János Pintz
year: 2026
title: Oscillation of partial sums of the Möbius function and zeros of Riemann's zeta function
doi: null
url: https://arxiv.org/abs/2608.24878v2
claim: The preprint compares unsigned Möbius averages and interval maxima with a zero-dependent envelope on logarithmic scales. Its maximum upper bound applies to a specified point, but supplies neither a square-root-scale constant nor the signed prime-error tail bound at a selected Robin source.
strata_touched: []
license: citation-only
triage: anchor
---

# Unsigned Möbius envelopes and the signed source boundary

The primary is [arXiv:2608.24878v2](https://arxiv.org/pdf/2608.24878v2),
submitted 1 September 2026, with 23 pages and PDF SHA-256
`f2e2d49d3b1c8275bedeed534403fa5524d89171c80d8d015b47b7b43dd335b9`.
The arXiv metadata inspected on 7 October 2026 lists this version.
Theorems 2.1–2.2 and Corollaries 2.1–2.2, printed p.8, their definitions
on pp.4–8, and the revised contour estimates in §5 were inspected.
The main theorem statements also occur in v1; updating the cited version
does not assert a strengthened theorem. This is a primary-source scope
check, not an independent complete proof audit or Lean verification.

## The quantities and exact precision

$$
\begin{aligned}
M(x)&=\sum_{n\le x}\mu(n),\\
D_M(x)&=\frac1x\int_0^x|M(u)|\,du,\\
S_{M,\delta}(x)&=\max_{x^{1-\delta}\le u\le x}|M(u)|
                  \qquad(0<\delta<1),\\
Z(x)&=\max_{\substack{\rho=\beta+i\gamma\\\gamma>0}}
                         \frac{x^\beta}{\gamma},\\
\omega(x)&=\log\frac{x}{Z(x)}
           =\min_{\substack{\rho=\beta+i\gamma\\\gamma>0}}
                    \bigl((1-\beta)\log x+\log\gamma\bigr).
\end{aligned}
$$

Zeros are counted with the source's conventions. For a positive quantity
$U(x)$ put $\omega_U(x)=\log(x/U(x))$. The relevant clauses of
Theorems 2.1–2.2 give, for each fixed $\delta$ and $x\to\infty$,

$$
\omega_{D_M}(x)\sim\omega_{S_{M,\delta}}(x)\sim\omega(x),
\qquad
\log D_M(x)\sim\log S_{M,\delta}(x)\sim\log Z(x).
$$

The first comparison can be written as
$D_M(x),S_{M,\delta}(x)=Z(x)\exp(o(\omega(x)))$.
It does not say $D_M(x)/Z(x)\to1$ or supply a relative error estimate.
In particular it does not give a specified constant in a square-root-scale
bound. With $\Theta=\sup_\rho\Re\rho$, the paper's corresponding
logarithmic exponent is $\Theta$; setting it to $1/2$ would assume RH.

The paper also defines
$D(x)=x^{-1}\int_0^x|\psi(u)-u|\,du$ and
$S(x)=\max_{u\le x}|\psi(u)-u|$.
Corollaries 2.1–2.2 compare these **unsigned** quantities with the
Möbius quantities on the same two logarithmic scales. They do not identify
their point values, signs, or oscillation phases.

Only the $D_M$, $S_{M,\delta}$ and positive-height $Z$ clauses are used
here. Equation (1.26) uses $|\gamma|$ in the two-sided envelope $W$;
its repetition in (2.10) omits those modulus signs in the inspected TeX.
That repeated line is not used as a signed zero sum or as a sign supplier.

## Boundary of the FIB/Robin interface

For a specified $x>1$, one does have

$$
|M(x)|\le S_{M,\delta}(x).
$$

Thus the maximum's upper envelope applies at every specified point in its
range, including an authenticated FIB source or a Robin source's clock.
No exceptional-point sampling assumption is needed for this application.
Using the asymptotic logarithmic comparison at a fixed $A$ still requires
its large-$x$ premise; the comparison does not certify that this $A$
exceeds an effective cutoff.
The lower bound on the maximum instead locates some point in the interval;
it does not locate that point on a prescribed FIB family or at the selected
Robin source. An average magnitude is also not a signed cancellation bound.

For the [selected critical source](../Arith/caveney2012sacaga.md),
the [effective core application](polak2026finiterobinca.md) keeps
$A=\log N$ and requires a source-specific lower bound for

$$
\sqrt A\log A\,I_\psi(A),\qquad
I_\psi(A)=\int_A^\infty(\psi(u)-u)
                       \frac{1+\log u}{u^2\log^2u}\,du.
$$

The maximum bound above controls $M(A)$, not this signed infinite tail.
The prime-error maximum $S(u)$ also gives pointwise unsigned envelopes
for $\psi(u)-u$. Integrating those envelopes yields weaker absolute tail
bounds; the required normalized constant and an effective cutoff for that
constant are not supplied by the logarithmic comparisons.
The paper itself distinguishes the $1/\zeta$ singularities for $M$ from
the logarithmic-derivative singularities for the prime error, in §2,
equations (2.2)–(2.3). Sharing the zero-dependent logarithmic envelope
does not transport their coefficients or establish the required
source-specific lower bound for the weighted prime-error integral.

These are reusable magnitude estimates and precise source restrictions.
The remaining work is a signed, same-source transport or estimate;
reproving the envelope comparison would not supply it. This note gives
no new oscillation theorem, normalized signed bound, Robin verification
range, or RH proof.

## Exponential smoothing does not give a positive reconstruction of the Robin cutoff

A related primary is Songlin Han, *The Error in a Smooth Weighted Prime
Number Formula and Zero-free Regions for the Riemann Zeta Function*,
[arXiv:2505.23795v1](https://arxiv.org/pdf/2505.23795v1), submitted
26 May 2025. The inspected PDF has 20 pages and SHA-256
`12c69d640afd1742276303b2f59130c3262875dfe5ca990de1f6c75557d64139`.
Its definitions and equation (2), printed pp.1–2, use the actual
prime-power coefficients and the exponential error

$$
D_{\rm exp}(y)=\sum_{n\ge1}(\Lambda(n)-1)e^{-n/y},\qquad y>0.
$$

The cited classical Theorem A, printed p.2, bounds this by $O(\sqrt y)$
**under RH**. The source's further zero-free-region implications do not
supply an unconditional square-root bound or a signed estimate at the
selected Robin clock. The interface below uses its exponential weight,
not an assumed converse or an independent certification of its proofs.

### Keep the actual coefficients and the complete tail

At the [selected critical source](polak2026finiterobinca.md), keep
$A=\log N>2$, and put

$$
q(t)=\frac1{t\log t},\qquad k(t)=-q'(t),\qquad
w_A(n)=q(\max(A,n)).
$$

For every real $R>A$, finite summation gives the exact identity

$$
\begin{aligned}
\int_A^R(\psi(t)-t)k(t)dt
={}&\sum_{n\le R}(\Lambda(n)-1)
       [q(\max(A,n))-q(R)]\\
 &+\int_A^R(\lfloor t\rfloor-t)k(t)dt.
\end{aligned}
\tag{S1}
$$

Indeed, $\psi(t)-\lfloor t\rfloor=\sum_{n\le t}(\Lambda(n)-1)$;
interchange only this finite sum with the integral. The lower endpoint
for a term is $\max(A,n)$, and $\int_u^Rk(t)dt=q(u)-q(R)$.
Thus neither the prime powers nor the upper endpoint is discarded.

The [existing quantitative PNT supplier](../Weil/johnstonyang2022pnt.md)
ensures convergence of the original improper integral and of the ordered
series below. Also
$q(R)[\psi(R)-\lfloor R\rfloor]\to0$. Hence (S1) gives

$$
I_\psi(A)=\lim_{R\to\infty}\sum_{n\le R}(\Lambda(n)-1)w_A(n)
              +C_{\rm floor}(A),
\qquad
C_{\rm floor}(A)=\int_A^\infty(\lfloor t\rfloor-t)k(t)dt,
\tag{S2}
$$

with $-q(A)\le C_{\rm floor}(A)\le0$.
The series is an ordered, potentially conditional series, not a claim
of absolute coefficient convergence. This is a finite-summation
application to the existing Robin kernel, not a new explicit formula or
prime-distribution theorem.

### The coefficientwise positive-mixture bridge fails

Suppose a nonnegative measure $\nu_A$ on positive scales could reconstruct
these exact coefficient weights from Han's exponentials:

$$
w_A(n)=\int_{(0,\infty)}e^{-n/y}\,d\nu_A(y)
\qquad(n\ge1),
\tag{S3}
$$

with every displayed integral finite. Every such sequence is discretely
convex. For every integer $m\ge2$, linearity of the three finite integrals
gives

$$
w_A(m-1)-2w_A(m)+w_A(m+1)
=\int_{(0,\infty)}e^{-(m-1)/y}(1-e^{-1/y})^2d\nu_A(y)\ge0.
\tag{S4}
$$

But take $m=\lfloor A\rfloor\ge2$. The actual Robin weights have
$w_A(m-1)=w_A(m)=q(A)$ and $w_A(m+1)=q(m+1)<q(A)$, because
$q$ is strictly decreasing and $m+1>A$. Therefore

$$
w_A(m-1)-2w_A(m)+w_A(m+1)=q(m+1)-q(A)<0.
\tag{S5}
$$

Equations (S4)–(S5) exclude (S3), including at this actual source clock.
Allowing a nonnegative constant component does not help: its second
finite difference is zero. The same local obstruction holds for the
finite weights in (S1) when $R>m+1$, so it is not produced by dropping
the infinite tail. The argument is the usual convexity of positive
exponential mixtures applied to the particular cutoff weights; no new
general mixture theorem or originality is claimed.

Consequently a pointwise one-sided estimate for $D_{\rm exp}(y)$ cannot
be transported to (S2) by an exact coefficientwise nonnegative mixture
of these same exponential kernels. This statement concerns that bridge,
not every possible relation between the two actual arithmetic sums.
It does not exclude signed inversion, an additional correction term with
its own bound, Tauberian estimates, or a direct estimate for $I_\psi(A)$.
Those alternatives must retain $C_{\rm floor}$ and pay the full tail and
all reconstruction losses at the same source.
The [existing FIB dilation filter](verjovsky2026mobiussmoothing.md)
already gives norm estimates in a different coefficient problem; its
invertibility is not a substitute for (S3) or for sign control here.
No new signed Robin lower bound, finite verification range, Lean result,
or proof of RH is supplied by this obstruction.
