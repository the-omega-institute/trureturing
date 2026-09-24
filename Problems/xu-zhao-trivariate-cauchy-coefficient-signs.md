---
slug: xu-zhao-trivariate-cauchy-coefficient-signs
bibkey: xu2026rational
doi: 10.48550/arXiv.2609.11072
url: https://arxiv.org/html/2609.11072v1
triage: window
motivation_gids:
  - D5/S3/Weil/Probability/AnalyticLogarithmicContinuation
---

# Xu-Zhao Conjecture 1.3

## Problem

For every nonempty positive composition $k=(k_1,\ldots,k_d)$ and integer
$\ell\ge1$, put $F_k(z)=z^{-d}\operatorname{Li}_k(z)$ with its removable
value at zero, and
$C_n^{j;k;\ell}=[z^n](1-z)^{-j}F_k(z)^{-\ell}$ as in source equations
(7)-(8). Conjecture 1.3 asks for $C_n^{0;k;\ell}<0$ eventually. For every
fixed integer $j\ge1$ it also asks for $C_n^{j;k;\ell}>0$ eventually and,
if $k_1>1$, for
$C_n^{j;k;\ell}>\binom{n+j-1}{n}/\zeta(k)^\ell$ eventually.
The threshold may depend on $k,\ell,j$; the strict inequality and all
quantifiers are retained.

## Motivation

The frozen scalar-series analyticity supplier connects polynomial
coefficient bounds with the actual analytic generating series. The
composition disk theorem now supplies a noncircular source-specific
analytic reciprocal on the entire unit disk, needed before its Taylor
coefficients can be identified with the source's formal inverse.

## Gap

`CompositionZeroFree.result` is only the intermediate all-composition disk
theorem: absolute convergence, analyticity, nonvanishing, and positive
real part of the extended logarithmic derivative. Both source recurrences,
strict-index correspondence and exact zero order are established in its
dependency unit. The full conjecture is not proved and receives zero
solved-problem credit; there is no `OpenProblemResolutionClaim`.

`CompositionBoundary.result` additionally proves W03: every admissible
positive composition has summable normalized coefficients, a summable
full strict-tuple family with the same strictly positive total, and the
actual normalized source has this radial limit at one. The nested harmonic
bound and the unbounded comparison are proved, and the source quotient
identity is explicit. No summability or source-equivalence premise is
assumed. The empty tail is included.

`CompositionSlit.result` additionally constructs the actual all-composition
branch on the full slit domain, proves holomorphy, disk agreement, origin
normalization, exact depth-order vanishing, conjugation symmetry and both
origin-correct recurrences. It assumes no continuation or recurrence premise
and asserts no global slit nonvanishing. This is also an intermediate with
zero solved-problem credit.

`CompositionBanks.result` now proves the complete local Banks bridge for every
positive head, positive-entry tail and positive power $\ell$. It gives an
actual-branch nonvanishing radius $0<\rho<1$ around one, the reciprocal-power
endpoint on the full slit-domain filter, jointly continuous conjugate
extensions on the two closed half-collars, and strictly negative imaginary
part on the entire upper boundary interval $1+t$ for $0<t\le\rho$. For an
admissible head the endpoint is $\zeta(k)^{-\ell}$; for leading head one it is
zero. This is a local, composition-dependent collar theorem, not a general
power-log asymptotic.

`CompositionZeroFreeCollar.normalizedContinuation` now gives the actual
depth-normalized slit branch: it uses `CompositionDisk.normalized` at zero and
the actual continued branch divided by the exact depth power away from zero.
`CompositionZeroFreeCollar.result` proves agreement with the disk
normalization, analyticity on the full source slit domain, and, for every
positive composition, one composition-dependent $R_0>1$ on which this actual
normalized continuation is zero-free inside the slit domain. It asserts no
global slit-domain nonvanishing and no radius uniform over compositions.

The full Taylor or formal-inverse coefficient correspondence, the
finite-contour sign transfer, and the all-$j$/$\ell$ assembly remain unproved
here.
The eventual sign and strict binomial conclusions therefore remain open
in this repository. Preregistration:
https://github.com/the-omega-institute/trureturing/issues/9372.

## Route

Using the proved disk, admissible-boundary, slit, local Banks and zero-free
collar units, identify the Taylor coefficients of the actual normalized
continuation and its reciprocal powers with the source's formal inverse. A
finite contour must then transfer the strict upper-bank boundary sign to
eventual strict negativity. Eventual negativity together with the actual
finite radial limit yields absolute summability: bound finite sums with radial
weights first, then pass to radius one. Strict negative tails give the $j=1$
excess. A uniform positive radial lower bound gives eventually positive
partial sums, and repeated summation handles every fixed $j\ge2$.
No coefficient asymptotic equivalent or boundary derivative total is
assumed in this route.

## Falsifier

A positive composition and power with infinitely many nonnegative
$C_n^{0;k;\ell}$, or a fixed positive $j$ with infinitely many failures of
its required strict inequality, refutes the conjecture. A disk zero of
the actual normalized series would instead contradict the intermediate
formal theorem; replacing that series by a surrogate would test a
different object.

## Evidence

The Lean unit is `CompositionDisk.lean`, `CompositionRecurrences.lean`
and `CompositionZeroFree.lean` under
`D5/S3/AnalyticClosure/Polylogarithm/`. Its final declaration is
`CompositionZeroFree.result : CompositionDisk.diskStatement`.
The consumer quantifies only over a positive head and a list of positive
tail entries; no analytic recurrence or zero-free premise is supplied.
The explicit extension has $Q(0)=d$, and the zero of `li` has order exactly
$d$ with positive minimal-tuple leading coefficient. The companion
Library notes record source correspondence and classical attribution.

`CompositionBoundary.lean` adds the single theorem
`CompositionBoundary.result`, using the frozen `CompositionDisk`
definitions. The unbounded harmonic comparison supplies both summability
claims. Grouping by the largest strict index and deleting only the proved
zero prefix identifies the totals. Dominated convergence applies to the
actual normalized series on real radii below one.

`CompositionBanks.lean` adds the single public theorem
`CompositionBanks.result`. Its five private implementation modules supply
source-weight induction, radial and arc bounds, leading-block transport,
leading closure and the ordinary-head transport step. The theorem quantifies
over `head : PNat`, `tail : List PNat` and `ell : PNat`; its one radius is
used simultaneously for actual-branch nonvanishing, the full-slit endpoint,
both continuous closed half-collars, their conjugation identity and the
strict upper boundary sign for every positive $t$ up to that radius.

`CompositionZeroFreeCollar.lean` adds exactly the public definition
`CompositionZeroFreeCollar.normalizedContinuation` and theorem
`CompositionZeroFreeCollar.result`. The radial argument differentiates
$H(r)=|\operatorname{continued}_k(r\zeta)|^2$ and obtains
$H'(r)=2|F(r)|^2\operatorname{Re}Q(r\zeta)/r>0$, avoiding an endpoint
logarithm. Disk agreement glues the removable origin, the actual Banks theorem
at $\ell=1$ patches the neighborhood of one, and compact thickening of the
closed unit disk inside their open union gives the claimed $R_0>1$.

## Triage

`window`: the complete conjecture remains the target. The source settles
all-one compositions for every $\ell\ge1$ by the all-one identity and
Theorems 1.1 and 8.2; depth one and depth two at $\ell=1$ by Theorems 9.6
and 9.9, respectively; and depth one at $\ell=2$ by Corollary 9.11.
The present disk, admissible-boundary, slit, Banks and zero-free collar results
are intermediates, not a new resolution of those known cases or of the full
conjecture. The collar is an ordinary auxiliary result with source-specific
escape content; it does not use the open-problem-resolution exception and
does not mark this dossier resolved. Taylor/formal-inverse correspondence,
contour sign transfer and the all-$j$/$\ell$ assembly remain the completion
boundary.

## ASSUMED-UNVERIFIED

Worldwide unresolved status and priority are not established by the
bounded literature assessment. The first-contact argument is classical,
and no novelty claim is attached to it. This auxiliary makes no worldwide-
priority claim; caller-owned PR, CI and lifecycle decisions remain separate.
