---
bibkey: alaoglu1944highly
authors: Leonidas Alaoglu and Paul Erdos
year: 1944
title: On highly composite and similar numbers
doi: 10.2307/1990319
claim: The classical exchange argument assigns larger exponents to smaller primes in the factorization of a superabundant number; its local reciprocal geometric sum comparison is formalized here for arbitrary real bases greater than one.
strata_touched:
  - D5/S3/Arith/RobinExponentSwap
license: citation-only
triage: anchor
---

# On highly composite and similar numbers

Transactions of the American Mathematical Society 56 (3), 448-469.

The literature source is the classical nonincreasing-exponent argument for
superabundant numbers. The local exchange inequality compares products of
reciprocal geometric sums when two prime exponents are exchanged. The Lean
statement isolates this inequality and states its algebraic argument for all
real bases greater than one, without requiring primality. This real-base
formulation is an explicit generality choice, not a claim that the paper
states a separate theorem with precisely those real quantifiers.

This note attests the classical argument and its local factors. It does not
claim that this module proves the existence of a Robin counterexample, the
structure of every superabundant integer, or the Riemann hypothesis criterion.

Verified bibliographic locator: https://doi.org/10.2307/1990319.
Primary text: https://www.renyi.hu/~p_erdos/1944-03.pdf, section 2,
Theorem 1 and its proof, checked on 2026-09-06. That theorem states the
nonincreasing order of the prime exponents. Its proof compares a
superabundant number with the smaller number obtained by transferring one
prime factor, and uses the decrease of `(x^n - 1) / (x^n - x)` in the base
and exponent. This is the provenance of the exchange argument, rather than
a verbatim statement of the real-base full-swap inequality proved here.

## Verified locator

- DOI: https://doi.org/10.2307/1990319
