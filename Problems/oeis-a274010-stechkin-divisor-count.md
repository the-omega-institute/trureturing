---
slug: oeis-a274010-stechkin-divisor-count
bibkey: israeloudra2020a274010
doi: null
url: https://oeis.org/A274010
triage: theorem
motivation_gids:
  - D5/S3/Arith/StechkinFunctionDivisorCount
---

# Oudra's divisor-count formula for the Stechkin function

## Problem

OEIS A274010, NAME (`%N`, verbatim):

> Boris Stechkin function: a(n) is the number of m with 2 <= m <= n and floor(n(m-1)/m) divisible by m-1.

Ridouane Oudra's FORMULA conjecture (`%F`, verbatim):

> Conjecture: a(n) = tau(n) + tau(n-1) - 2, for n>=2. - _Ridouane Oudra_, Feb 28 2020

AUTHOR (`%A`, verbatim):

> _Robert Israel_, Jun 06 2016

The formal definition counts the natural numbers `m` in the closed interval
from two through `n` for which `m-1` divides the natural quotient
`n*(m-1)/m`. Natural division is the floor of the corresponding nonnegative
rational quotient. For every `n >= 2`, the formal theorem states
`stechkinFunction n + 2 = n.divisors.card + (n-1).divisors.card`.
Both divisor finsets contain one, so their cardinalities sum to at least two;
the subtraction-free equality is therefore equivalent to the quoted formula.

## Motivation

The formula identifies a filtered divisibility count with the sum of two
adjacent divisor counts. It gives a closed arithmetic description of every
term of the sequence rather than a finite-prefix verification.

## Gap

The OEIS entry labels the formula as a conjecture and carries no settlement
line. Its cited bibliography predates the formula, and the linked table gives
values rather than a proof. Exact repository and pinned-library searches found
no existing declaration of the definition, formula, source predicate, or
divisibility equivalence used below.

## Route

Reindex the defining interval by `k=m-1`. For `1 <= k < n`, Euclidean
division shows that `k` divides `n*k/(k+1)` exactly when `k+1` divides `n` or
`n-1`. This identifies the filtered interval with the disjoint union of the
divisors greater than one of those adjacent numbers. Taking cardinalities and
restoring the omitted divisor one on both sides gives the formula.

## Falsifier

Any natural number `n >= 2` for which the filtered count plus two differs from
the sum of the two divisor counts would refute the result. Agreement on any
finite initial range would not establish the universal statement.

## Evidence

- Module: `D5/S3/Arith/StechkinFunctionDivisorCount.lean`.
- `stechkinFunction` formalizes the quoted interval, quotient, divisibility
  predicate, and cardinality.
- `result` proves the universal adjacent divisor-count equality.
- The theorem's axiom closure is `[propext, Classical.choice, Quot.sound]`.

## Triage

`theorem`; resolution `proved` for every natural number `n >= 2`.

## ASSUMED-UNVERIFIED

The source quotations, contributor attribution, absence of an OEIS settlement
line, bibliography date, hyperlink description, and external-search readings
are attributed evidence without independent verification. Historical openness
beyond the checked sources remains unverified; no exhaustive literature or
priority claim is made.
