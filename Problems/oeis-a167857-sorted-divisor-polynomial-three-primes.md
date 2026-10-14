---
slug: oeis-a167857-sorted-divisor-polynomial-three-primes
bibkey: noe2009a167857
doi: null
url: https://oeis.org/A167857
triage: theorem
motivation_gids:
  - D5/S3/Arith/SortedDivisorPolynomialThreePrimes
---

# OEIS A167857: three distinct prime divisors

## Problem

The Online Encyclopedia of Integer Sequences, A167857, T. D. Noe, defines
numbers whose divisors are represented by an integer polynomial:

> That is, these numbers n have the property that there is a polynomial f(x) with integer coefficients whose values at x=0..tau(n)-1 are the divisors of n, where tau(n) is the number of divisors of n.

The published question is:

> Are there terms with three distinct prime divisors?

The exact target is existence of a positive natural n with
`n.primeFactors.card = 3` and `f : Polynomial Int` such that, for every
`j < n.divisors.card`, evaluation at the integer cast of j equals entry j
of the actual increasingly sorted finset of all positive divisors of n.
Both factor count and divisor list belong to this same n. The list has no
duplicates; the inputs start at zero. No minimum, degree bound, numerical
candidate, divisor subset, alternate order or rational-only conclusion is
imposed. Preregistration: https://github.com/the-omega-institute/trureturing/issues/16601.

## Motivation

This is the original published existence question, classified as Tier 1 in the
prospective registration. Its age is not evidence of novelty or priority.

## Gap

Bounded source qualification inspected the current public/internal/history
snapshots, seven direct neighbors, the Noe table, relevant repository source
contracts, literature and official exact-target ownership queries. No
whole-equivalent settlement or matching owner was found in those inspected
scopes. Crossref/OpenAlex searches used top pages, some StackExchange pages
remain unread, and GitHub divisor-polynomial search returned 100 metadata hits
of 160. Unindexed/offline ownership remains unverified. This does not establish
worldwide absence or priority.

## Route

Choose distinct primes p<q<r, each 1 modulo 5040, using the pinned Mathlib
arbitrarily-large congruent-prime theorem. The same product n=p*q*r has eight
positive divisors, all 1 modulo 5040. Let d_i be the actual increasing divisor
list entry at i. The signed nodal denominator
`D_i = product_(j != i) (i-j)` is nonzero and divides 5040 for each of the eight
indices. Define `c_i=(d_i-1)/D_i` in Int and
`f=1+sum_i c_i*product_(j != i)(X-j)` in Polynomial Int. Its rational image is
the existing Lagrange interpolant plus 1, so the upstream node-evaluation
theorem and injectivity of the cast prove every required integer evaluation.

## Falsifier

A faithful refutation would negate the entire original existential, for all
positive n with three distinct prime factors and every integer-coefficient
polynomial. Failure of this route, one candidate or a finite search would not
refute that existential.

## Evidence

The exact source-to-quantifier mapping is embodied in
`D5/S3/Arith/SortedDivisorPolynomialThreePrimes.result`, with its mirrored
Blueprint Scribe. The construction reuses pinned Mathlib; the proof shape is
bind-only and the admission basis is open-problem-resolution. It is an
unbounded symbolic existence proof, not a finite candidate certificate.
The canonical frozen module contains seven included declarations. Complete-unit
independent review, draft publication, the full original-BASE local gate,
exact-head required CI, MERGED readback and subsequent dev verification remain
outstanding; no counted delivery is claimed.
The required information audit is unfinished: the compiled Reg source record
is `declared_unresolved` with `IE-C050 ClosedTruthReadout`,
`rule=source.observation_data`. Its missing source observation-data binding is
tracked at https://github.com/the-omega-institute/trureturing/issues/16620.

## Triage

### What the settlement shows

Proved by `D5/S3/Arith/SortedDivisorPolynomialThreePrimes.result`: the decisive
mechanism is a common residue modulus divisible by all eight
Lagrange nodal denominators. This forces integral coefficients while allowing
the actual sorted divisor order. Unproved in this delivery: a uniform extension
to arbitrary prime-factor counts, minimal n and optimal degree. The latter two
are outside the published question. No known-supplier, new-method or global
novelty credit is claimed.

## ASSUMED-UNVERIFIED

Frisch, Interpolation by Integer-Valued Polynomials, DOI10.1006/jabr.1998.7741:
author/publisher fulltexts403. Chabert, About Polynomials Whose Divided
Differences are Integer-Valued on Prime Numbers, DOI10.1080/00927872.2014.897588:
publisher403, authoritative exact-title HAL query0; full theorem conditions
unverified. The Volkov–Petrov paper arXiv:1108.3212v1 concerns quotient-field
integer-valued interpolation; the fixed-divisor survey DOI10.5802/cml.54
concerns gcd/ideal conditions; the inspected scopes do not settle this whole
ordered-list question. MathOverflow169083/169084 is conditional on integral
existence. Math.SE4453859/1467910 gives general interpolation criteria;
Math.SE4789468 uses divisor inputs and is a different problem.

Recent Zenodo DOI10.5281/zenodo.23148134 has an authoritative abstract about
prime patterns, with fulltexts403. Immutable OEIS views403, two new arXiv429,
prior arXiv export/timeouts/exact-ID/228/newest50/178-unread limits, Semantic
Scholar429, two Crossref429, zbMATH403 and the AMS page870 mirror404 remain
named access/scope gaps. BeautifulSoup/pdftotext were unavailable; pypdf
missing-fontTools warnings limit extracted glyphs. Transport failures do not
prove absence. The A073103 ID/description mismatch is excluded as a premise.
