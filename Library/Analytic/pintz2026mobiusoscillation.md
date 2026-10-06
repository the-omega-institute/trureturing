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
