---
slug: oeis-a090825-bernoulli-integrality-refutation
bibkey: cloitre2004a090825
doi: null
url: https://oeis.org/A090825
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation
---

# Refutation of Cloitre's A090825 Bernoulli-integrality conjecture

## Problem

OEIS A090825, NAME (verbatim):

> Nonprimes n such that (3/2)*(1/n)*(2*n+1)*(3^n+1)*B(2*n) is an integer, where B(k) denotes the k-th Bernoulli number.

Benoit Cloitre's COMMENT of February 11, 2004 (verbatim):

> Conjecture: composite numbers with all prime factors in A053176 are in the sequence.

For natural numbers, define
`F(n) := (3/2)*(1/n)*(2*n+1)*(3^n+1)*B(2*n)` in the rationals and
`A053176(p) := Prime(p) and not Prime(2*p+1)`. The literal refuted statement
is: for every composite natural `n > 1`, if every prime divisor `p` of `n`
satisfies `A053176(p)`, then `F(n)` is an integer.

The separate COMMENT clause asserting `F(p) = 1 (mod p)` for primes, and the
question whether the subsequence beginning 91, 247 is finite, are not claimed
or assessed.

## Motivation

Cloitre's comment asserts a universal sufficient condition for membership in
A090825. A composite satisfying the stated prime-factor condition while its
rational value has a nontrivial denominator refutes that conjecture directly.

## Gap

Preregistration issue #7735 records searches dated September 14, 2026. OEIS
history revisions #1 through #13 contain no settlement of the conjecture since
2004, and the source PARI program checks only `n <= 750`. Exact searches of
arXiv and MathOverflow were checked for A090825; MathOverflow returned zero
results, while the arXiv surface did not return a parseable result count.

These bounded surfaces do not establish exhaustive literature coverage,
historical openness, or publication priority. No priority claim is made.

## Route

Take `n=833=7^2*17`. Its prime divisors are 7 and 17; the corresponding values
`2*7+1=15` and `2*17+1=35` are composite, so the prime-factor premise holds.
The von Staudt-Clausen theorem at index 1666 gives the relevant primes
`{2,3,239,1667}` and hence `v_239(B(1666))=-1`. Also
`3^833 = 1 (mod 239)`, so 239 does not divide `3^833+1`. The other factors
`3/2`, `1/833`, and 1667 all have 239-adic valuation zero. Therefore
`v_239(F(833))=-1<0`, so `F(833)` is not an integer.

## Falsifier

A proof of the literal universal `claim` would falsify this refutation. The
result instead supplies the instance 833 and proves that its 239-adic
valuation is negative despite satisfying every hypothesis of the claim.

## Evidence

- Lean module:
  `D5/S3/Arith/Congruence/CloitreBernoulliIntegralityRefutation.lean`.
- Main theorem: `result : Not claim`, with exactly the std3 axioms `propext`,
  `Classical.choice`, and `Quot.sound`.
- The Stage B profile took 8.76 seconds wall time and 1.23 seconds of
  cumulative type checking, with maximum resident set size 2,716,631,040
  bytes.
- The proof derives `padicValRat 239 (bernoulli 1666) = -1` from
  `Bernoulli.vonStaudt_clausen` and an explicit divisor/prime classification,
  then propagates it to `padicValRat 239 (F 833) = -1`. It decides only the
  twelve divisors of 1666 rather than a 1668-element prime filter.

The orchestrator independently computed the reduced denominator
`den(F(833))=239`, `3^833 mod 239=1`, the von Staudt-Clausen prime set
`{2,3,239,1667}`, and the A053176 premise for the prime factors 7 and 17.

These exact computations corroborate the symbolic proof. They do not assert
a classification of all counterexamples.

## Triage

`theorem`. The symbolic 239-adic obstruction at 833 refutes the literal
universal conjecture. No claim is made about the second COMMENT clause, the
subsequence question, or publication priority.

## ASSUMED-UNVERIFIED

Historical openness after the checked OEIS history, arXiv, and MathOverflow
surfaces is `ASSUMED-UNVERIFIED`. Exhaustive literature coverage and priority
are not claimed. The arXiv search did not yield a machine-readable count.
