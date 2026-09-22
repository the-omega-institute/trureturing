---
slug: oeis-a132393-kurkov-nested-stirling-identity
bibkey: kurkov2026a132393
doi: null
url: https://oeis.org/A132393
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion
---

# A132393: Kurkov's nested Stirling identity

## Problem

> Conjecture: T(n+m+1,m+1) = (n+m)! * (Product_{i=1..m} (n+i)^i) * Sum_{j_1=0..n} Sum_{j_2=0..j_1} ... Sum_{j_m=0..j_{m-1}} (-1)^(n*m + j_1 + j_2 + ... + j_m) * (Product_{1 <= q < p <= m} (j_q - j_p + p - q)^2) * Product_{t=1..m} (n+t-1)_{j_t} / ((n-j_t+t)^(m+1) * (j_t+m-t)!) where (x)_{n} is the falling factorial defined as (x)_{n} = Product_{k=0..n-1} (x-k). - _Mikhail Kurkov_, May 24 2026

The target quantifies over every natural n and every m >= 1, with equality
in the rationals. T is the unsigned Stirling number of the first kind.
The chain is n >= j_1 >= ... >= j_m >= 0. Falling factorial means the
displayed descending product. This is the exact source assertion registered
before formal probes in
https://github.com/the-omega-institute/trureturing/issues/9456.

## Motivation

This is the first-tier 2026 external conjecture selected by programme 8654.
The admission basis is `open-problem-resolution`; the public delivery is
the source definitions and one theorem, `result`. The elaborated proof has
`proof_shape: content`: the source chain/subset equivalence, normalization
and determinant recurrence require construction and induction beyond
instantiation, projection and normalization of the existing suppliers.
No classical identity or bind-only companion is separately exported.
Independent source, admission and proof review remains part of the
caller-owned lifecycle; this dossier does not claim independent approval or
merged status.

The direct frozen mathematical supplier is
`D5/S1/Recurrence/Parity/StirlingPowerFactorialPrimePeriod.stirling2_inclusion_exclusion`,
whose module statement identity at the assigned base is
`sha256:de3301b051609b0cfd4822db18707fa5d6b43e7a78e550dda3911b35c172da11`.
The declaration statement identity in the current Lean report is
`sha256:2508e114d7ae0d003f3f1c2ca5079a26811c8ed501add6239b68109ce2a28efb`.
This supplier motivates the zero and negative moment evaluations below.
Mathlib supplies determinant operations and the Vandermonde evaluation.
The exact external Cauchy-Binet supplier is reused with attribution and full
license, as recorded in the Library note. No new dependency, axiom or
toolchain change is required.

## Route

Let N=n+m and l_t=n-j_t+t. A decreasing source chain gives
1 <= l_1 < ... < l_m <= N. Conversely the t-th increasing element satisfies
t <= l_t <= n+t; j_t=n+t-l_t reconstructs the unique source chain.
This is proved as an equivalence of finite types, including the empty
extension used inside the proof.

The falling factorial becomes (n+t-1)!/(l_t-1)!, and j_t+m-t=N-l_t.
The prefactor identity
product_i (n+i)^i times product_t (n+t-1)! = (N!)^m,
together with binomial factorial cancellation, gives
N! times (-1)^(m(m-1)/2) times the subset sum of
Delta(L)^2 product_l [(-1)^(l-1) choose(N,l)/l^m].
The source sign is verified by an even difference of integer exponents.
Vandermonde differences remain signed rational differences.

Apply the exact rectangular Cauchy-Binet supplier to the power matrix and
its weighted transpose. Mathlib evaluates each minor as a Vandermonde
determinant. The resulting matrix has entries mu_(m-i-j), with i,j
zero-based and
mu_k(N)=sum_(l=1..N) (-1)^(l-1) choose(N,l) l^(-k).
Here k is an integer, so negative moments are not truncated.

Frozen inclusion-exclusion proves mu_0(N)=1 and mu_(-r)(N)=0 for
0<r<N. Pascal's binomial identity proves, for every integer k,
(N+1) mu_(k+1)(N+1) = (N+1) mu_(k+1)(N) + mu_k(N+1).
This recurrence is an exact alternative to deriving the same complete
homogeneous moments by partial fractions.

Reverse the rows and cancel the reversal sign. Write H(N,d) for the matrix
with entry mu_(1+i-j)(N). Multiplying H(N+1,d+1) by the unit lower
bidiagonal matrix with subdiagonal -1/(N+1) changes it to H(N,d+1)
plus a last-column correction at its bottom entry. The nonpositive
moments justify that correction when d+1 <= N+1. Expanding this column
and its boundary cofactor yields
det H(N+1,d+1)=det H(N,d+1)+det H(N,d)/(N+1).
This is the elementary symmetric recurrence, obtained directly without
assuming a symmetric-function determinant identity.

Cauchy-Binet also proves det H(N,m)=0 for m>N: the required m-element
subsets of the N nodes do not exist. At m=0 the determinant is one.
Induction using these boundaries and the recurrence proves
N! det H(N,m)=stirlingFirst(N+1,m+1) for all N,m.
Together with the exact source reduction this proves the target.

## Gap

The Library note records the primary locator and bounded prior-art status.
The preregistration's audits found no equivalent resolution in their inspected
literature or Lean result corpora, subject to the ASSUMED-UNVERIFIED limits
below. The classical component identities carry no novelty claim.

## Falsifier

A natural n and m >= 1 with unequal literal rational sides would refute the
assertion. Fixed-m cases, finite numerical agreement and an assumed
determinant evaluation cannot establish the quantified result.

## Evidence

The Lean declaration
`D5.S1.Recurrence.Algebraic.KurkovNestedStirlingIdentity.result`
has exactly the target parameters and no conclusion-bearing hypothesis.
Its proof uses signed rational arithmetic and integer moment indices.
The proof-local calculations are retained on its live derivation path.
Formal and governance states are supplied by the canonical build and
admission tools, not by this narrative.

## Triage

`theorem`; the target is the full quantified source assertion. Independent
source, proof and admission review, final remote CI and merge remain pending
with the caller. No programme resolution credit or completed project delivery
is claimed by this producer preparation.

## ASSUMED-UNVERIFIED

The primary-source reading and prior-resolution searches are inherited from
the supplied implementation and preregistration conclusions; this metadata
finalization does not independently repeat them. The bounded audit inspected
the relevant Krattenthaler statements but not the cited original Neuwirth
proofs, and inspected Deb-Sokal only at abstract/introduction level, as
recorded in the Library note. The inspected literature and Lean corpora do
not rule out unindexed literature, textbooks, private allocations or later
solutions. Historical unresolved status outside those searched surfaces and
worldwide priority are unverified. Kernel closure does not establish those
claims or replace independent source-fidelity and admission review.
