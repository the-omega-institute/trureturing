---
slug: xu-zhao-trivariate-cauchy-coefficient-signs
bibkey: xu2026rational
doi: 10.48550/arXiv.2609.11072
url: https://arxiv.org/html/2609.11072v1
triage: theorem
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

The scalar-series, disk, boundary, slit and local Banks results connect the
strict-largest-index source to an analytic reciprocal. Finite-contour
transfer and signed-prefix Abel summation then establish the eventual
signs of the original ordinary coefficients.

## Gap

`FiniteSlitAdmissibleSmoothing.full_result` proves all of Conjecture 1.3:
eventual strict negativity at $j=0$ for every positive composition and
$\ell\ge1$, eventual strict positivity for each fixed $j\ge1$, and the
strict binomial excess for admissible heads. The quantifiers include an
empty tail and leading head one; no additional analytic, zero-free or
radial-margin assumption is imposed. Its owning Scribe attaches the single
`OpenProblemResolutionClaim` with `ResolutionKind.Proved` to `full_result`
and this dossier's exact slug.

The conclusion is eventual with parameter-dependent thresholds. Effective
or uniform thresholds and coefficient asymptotic equivalents are not
established. Worldwide literature completeness and priority remain
ASSUMED-UNVERIFIED. Preregistration:
https://github.com/the-omega-institute/trureturing/issues/9372.

## Route

The disk, admissible-boundary, slit, local Banks and zero-free collar results
supply one actual normalized continuation. The finite-slit contour identity
pairs conjugate banks and transfers their strict sign to eventual negative
Taylor coefficients. `FiniteSlitOrdinaryCoefficients.result` identifies these
with the ordinary coefficients of the source's formal inverse, using the
nonzero positive constant and uniqueness of analytic power series.

Finite radially weighted windows first bound the negative tail, yielding
absolute summability and the exact endpoint total. The first smoothing
excess is the ordinary partial sum minus that endpoint. A positive radial
margin, proved separately for admissible heads and leading head one, feeds
the signed-prefix Abel theorem and repeated summation for every fixed
$j\ge1$. The entire signed finite prefix is retained. No coefficient
asymptotic equivalent or boundary derivative total is assumed.

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
`CompositionBanks.result`. Its five implementation modules supply
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

The finite-slit coefficient chain consists of `FiniteSlitBankMoments`,
`FiniteSlitCompositionMoments`, `FiniteSlitCircleDefect` and
`FiniteSlitCoefficientIdentity`. Compact interior bank mass dominates the
outer geometric error; the proved rectangle identity and conjugate pairing
identify the signed bank integral with the actual Taylor coefficient.
`FiniteSlitOrdinaryCoefficients.result` then proves both coefficient
agreement with the reciprocal derivative divided by $n!$ and convergence
to that same reciprocal on the disk. The ordinary coefficient itself has
no additional factorial.

`FiniteSlitOrdinaryEndpoint.result` proves the absolute-summability and
endpoint bridge. `FiniteSlitOrdinarySmoothing.result` converts an actual
positive radial margin into all fixed smoothing orders while keeping the
full finite signed prefix. `FiniteSlitRadialMargin.result` derives the
admissible margin from the positive source coefficients and their actual
strict multiple-zeta total.

`FiniteSlitAdmissibleSmoothing.full_result` combines the admissible theorem
with the leading-one branch. In that branch the original remainder
controls give the logarithmic norm bound for the actual continued source.
Source agreement retains the factor $r^{d\ell}$; logarithmic decay gives
an eventual reciprocal margin of one, and the endpoint is zero. The theorem
therefore has no extra growth or margin hypothesis.

Ten escape audits remain unfinished, including both admissible and full
smoothing results. Their retained Reg proofs supply partial evidence, but
not a lawful enrolled-template readout, complete dependent-family and
observational-dependence proof, or source-selection/current-contract
certificate. No `declared_validated` status is asserted. The linked audit
exception is disclosed in
https://github.com/the-omega-institute/trureturing/issues/9372#issuecomment-6587797415
and
https://github.com/the-omega-institute/trureturing/issues/23926#issuecomment-6587801709.

## Triage

`theorem`: the exact full result proves the source conjecture with all
composition, power and fixed-order quantifiers. The source already proves
all-one compositions for every $\ell\ge1$ by the all-one identity and
Theorems 1.1 and 8.2; depth one and depth two at $\ell=1$ by Theorems 9.6
and 9.9; and depth one at $\ell=2$ by Corollary 9.11. Those known slices
and the classical analytic ingredients retain their attribution.

The proved mechanism combines strict bank-sign transfer with a radial
margin and signed-prefix Abel summation. The admissible branch gives the
strict baseline above the multiple-zeta endpoint; the leading-one branch
has zero endpoint and still yields every fixed positive smoothing order.
This proves the complete stated event without assuming a general
power-log expansion. Effective thresholds, uniformity over parameters,
asymptotic equivalents and sharpness remain unproved; they are separate
questions. No further source-paper consequence is asserted without its
own correspondence check.

## ASSUMED-UNVERIFIED

Worldwide unresolved status and priority are not established by the
bounded literature assessment. The first-contact and contour ingredients
retain their classical attribution. The inaccessible 2014 and 2023
publisher bodies have not been cleared by this result. No global novelty
or priority claim follows from the formal proof or the supplied search.
