---
slug: oeis-a265714-positive-threshold-common-minimum
bibkey: krizek2015a265714
doi: null
url: https://oeis.org/history/view?seq=A265714&v=23
triage: theorem
motivation_gids:
  - D5/S3/Factorization/ReciprocalSigmaThreshold.result
---

# Common positive threshold minima for reciprocal-sigma sums

## Problem

> a(n) = the smallest number k such that floor(Sum_{d|k} 1/sigma(d)) = n.

> Conjecture: a(n) is also the smallest number k such that Sum_{d|k} 1/sigma(d) >= n.

— Jaroslav Krizek, OEIS A265714, revision 23.

This dossier anchors exactly the common-minimum conjecture. For every
natural r>0, let g(k) be the exact rational sum of 1/sigma(d) over all
positive divisors d of the positive natural k, where sigma(d) is the
sum of all positive divisors of d. The sets
{k>0 : floor(g(k))=r} and {k>0 : g(k)>=r} must both be nonempty and have
the SAME least element. The floor is ordinary floor, r=1 is included,
and neither r nor k has a finite upper bound. There is no additional
existence or integrality premise. The source's separate integrality
question and proposed numerical minima are outside this single assertion.

## Motivation

The two predicates ask respectively for a first floor level and a first
threshold crossing of the same exact divisor sum. Their equivalence at
the least argument is a first-tier externally named OEIS conjecture.
The unchanged whole assertion is preregistered at
https://github.com/the-omega-institute/trureturing/issues/23157#issuecomment-6469463476.
The frozen theorem
`D5/S3/Factorization/ReciprocalSigmaThreshold.result` addresses precisely
this assertion.

## Gap

Existence of arbitrarily large values alone does not exclude a first
crossing that skips the desired floor level. The needed estimate controls
the overshoot at the least crossing. The bounded source, repository,
pinned Mathlib and selected third-party Lean searches found arithmetic
suppliers but no exact prior whole-result supplier in the searched scope.
This is not an exhaustive worldwide openness or priority claim.

## Route

Prime divisor terms give a lower bound by sums of 1/(p+1). Divergence
of the reciprocal-prime sum supplies a positive argument reaching every
threshold. Choose the least positive m with g(m)>=r. If m=1, g(1)=1
settles the floor bound.

Otherwise take the largest prime divisor P of m. Multiplicativity,
the prime-power bound g(p^a)<=p/(p-1), and the telescoping product over
the integers from 2 to P give g(m)<=P. Deleting one copy of P gives a
positive q<m with g(m)<=g(q)(1+1/(P+1)). Minimality gives g(q)<r;
since r<=P, the estimates imply r<=g(m)<r+1. Hence floor(g(m))=r.
Every positive k with floor(g(k))=r also reaches r, so this same m is
least for both predicates.

Krizek posed the conjecture. Israel's prior observations include
multiplicativity, the prime value, divergence and existence of each level.
The prime-power expansion is elementary; the common-minimum proof is a
repository derivation, without a claim of literature priority.

## Falsifier

A positive natural r for which either set is empty or the two least
elements differ would refute the complete assertion. A finite check,
a guessed minimum, an integrality assertion or a conditional-existence
version cannot settle the unbounded statement.

## Evidence

`D5/S3/Factorization/ReciprocalSigmaThreshold.lean` defines the exact
rational function `g`, the complete proposition `claim`, and proves
`result : claim`. The result's statement identity is
`sha256:c20fbd403ccd97115b5dc48ee1e2b1f3f84739cb14169b914e3d9e796663f622`.
Its accepted axiom closure is `Classical.choice`, `Quot.sound`, and `propext`.

All seventeen proof declarations are bind-only. The four definitions are
necessary and the sixteen private support lemmas have live consumers.
The retention basis is `open-problem-resolution`; no escape witness is
certified. The unbounded symbolic proof delivers no bounded enumeration,
checker, numerical reduction or certified finite instance, so its utility
classification is `none`.

The faithful compiled Reg mirror remains `declared_unresolved`, with
`IE-C050 / source.absent_occurrence` and no accepted binding certificate.
The missing raw selectors, complete-source reconstruction and current
binding are disclosed under CLAUDE section 3.9 at
https://github.com/the-omega-institute/trureturing/issues/23192.
Compilation of that mirror does not establish `declared_validated`.

## Triage

The frozen theorem
`D5/S3/Factorization/ReciprocalSigmaThreshold.result` proves the entire
positive-threshold common-minimum statement. The typed Scribe resolution
binds this one theorem to this one source conjecture. Semantic fidelity,
formal admission, required checks and publication retain their separate
roles.

### What the settlement shows

The decisive mechanism is the combination of the largest-prime upper
bound and the smaller prime-deletion witness at the first crossing.
It excludes overshoot of a whole integer interval and identifies both
first occurrences for every positive r, including r=1. These conclusions
are carried by the theorem above; no numerical minimum is supplied.

No condition beyond positivity is added to the source's thresholds or
arguments. The argument concerns this exact reciprocal-sigma function;
no extension to arbitrary weighted divisor sums is claimed. The source's
integrality question and proposed later numerical minima remain outside
the theorem, and no other source result is changed by this resolution.

## ASSUMED-UNVERIFIED

Source-to-Lean fidelity is a semantic review obligation. Bounded source
and library qualification does not prove global absence of another proof.
The unresolved Reg binding is not a mathematical refutation or a validated
escape registration. No claim of independent discovery, model diversity,
worldwide openness or priority follows from the typed resolution.
