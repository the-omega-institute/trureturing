---
slug: oeis-a394407-totient-tau-primes-huber
bibkey: huber2026a394407
doi: null
triage: theorem
motivation_gids:
  - D5/S3/Arith/OeisA394407TotientTauPrimes.result
url: https://oeis.org/A394407
---

# Huber's prime conjecture for OEIS A394407

## Problem

Felix Huber's OEIS A394407 has the Name:

> Positive integers k such that there is no m < k with phi(m)/tau(m) = phi(k)/tau(k).

Its Comment states:

> Conjecture: All primes p != 3 are in the sequence; equivalently, for every prime p != 3 there is no m < p with phi(m)/tau(m) = phi(p)/tau(p) = (p - 1)/2; equivalently, the sequence is a supersequence of A045344.

The source is an explicitly stated conjecture in an approved OEIS entry. The
settled proposition is the first form of that conjecture, preregistered in
[#18591](https://github.com/the-omega-institute/trureturing/issues/18591).
For positive integers, write $r(m)=\varphi(m)/\tau(m)$ with rational division.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Quotient phi(m)/tau(m) | `ratio m` | `Nat.totient m` divided by `m.divisors.card`, with both cast to rational numbers. |
| Positive integers k | First conjunct of `IsTerm k` | Zero is excluded. |
| No smaller m has the same ratio | Second conjunct of `IsTerm k` | Every positive natural m less than k is compared; no search bound is imposed. |
| All primes p != 3 | `claim` | Universal natural p, `Nat.Prime p`, and p different from 3. |
| Membership in the sequence | Conclusion `IsTerm p` of `result` | The first-occurrence predicate is unchanged. |

The positive domain for m follows the sequence's positive-integer convention.
Lean totalizes the ratio at zero to zero; no zero input enters the claim.

## Motivation

`D5/S3/Arith/OeisA394407TotientTauPrimes.result` proves the preregistered
`claim`. A prime's totient and divisor count give $r(p)=(p-1)/2$.
The source note is `Library/Factorization/huber2026a394407.md`.

## Gap

The universal prime-membership conjecture is settled. Classification of composite
terms and a separately formalized equality characterization are outside this
result. Literature completeness is `ASSUMED-UNVERIFIED`.

## Route

For prime $p$, its positive divisors are $1,p$, hence $r(p)=(p-1)/2$.
If $m=1$, then $r(m)=1$, and equality forces $p=3$.
If $2\le m<p$, then $\tau(m)\ge2$ and $\varphi(m)<m$; as $m+1\le p$,

$$r(m)\le\frac{\varphi(m)}2<\frac{p-1}2=r(p).$$

The result applies Mathlib's `Nat.totient_prime`, `Nat.totient_lt`, and
`Nat.Prime.divisors`, together with finite-set membership/cardinality facts
and rational normalization. It has no D5 imports or direct frozen D5 dependencies.

## Falsifier

A prime $p\ne3$ and a positive integer $m<p$ with $r(m)=r(p)$ would contradict
`result`. The collision $r(1)=r(3)=1$ shows why the exclusion is necessary.

## Evidence

The kernel-checked declaration is
`D5/S3/Arith/OeisA394407TotientTauPrimes.result : claim`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The two source fidelity examples are compiled in the module.
The result's proof shape is bind-only; its admission basis is
`open-problem-resolution (#18591; Proved)`, with no separate escape witness.

The four-slot escape audit for `result` is unfinished:
[issue #19902](https://github.com/the-omega-institute/trureturing/issues/19902).
No faithful compiled registration is delivered. Homogeneous pointwise
disequality and guarded equality templates do not directly read this guarded,
nested conjunction and disequality; the dependent-family reconstruction,
source-selection and sensitivity evidence is not supplied.

Experiment: [totient-to-divisor-count check](https://github.com/the-omega-institute/trureturing-experiments/tree/e501256d979a18522f95424d4e7f12f2c9e916ae/docs/reports/oeis-a394407-totient-tau-primes).
Command: `python3 docs/reports/oeis-a394407-totient-tau-primes/check.py 100000`
from that experiments repository; exit 0. Script SHA-256:
`c1829976fcf4650423d592d864a4c7fe262215ac543f16a6b24dbae3b320ff45`.
For $N=100000$, there are 26829 terms below N, the first 64 published terms
match, no prime other than 3 below N is missing, 3 is not a term, and
$r(m)\le(m-1)/2$ holds for every $2\le m<N$. These are finite computed
checks, independent of the universal Lean proof.

## Triage

### What the settlement shows

- **Proved in Lean:** every prime other than 3 is a term, by `result`.
  The decisive mechanism is the prime ratio $(p-1)/2$ and the strict bound
  for $2\le m<p$, with the sole exceptional collision at $m=1,p=3$.
- **Proved in prose:** every prime $p\ge5$ is a strict record among all
  positive $m<p$. For $m\ge2$, the inequality in Route is strict. For $m=1$,
  $r(1)=1<2\le(p-1)/2$. No separate Lean theorem for this strengthening
  is claimed.
- **Open formalization candidate:** for $m\ge2$, the equality
  $r(m)=(m-1)/2$ holds if and only if m is prime. This is not the statement
  of any separate delivered Lean theorem; the source's equality-case
  observation is retained as a neighbouring target.
- **Open:** characterize the composite terms of A394407. The prime theorem
  supplies no such classification.
- **Proved in prose, with a compiled source fidelity example:** the exclusion
  $p=3$ is necessary, since $1<3$ and $r(1)=1=r(3)$.
- **Computed:** precisely the finite experiment range and readings stated in
  Evidence. The computation does not establish any uniform extension.

The conjecture is stated in an OEIS entry rather than as a premise of further
source theorems. This settlement establishes the asserted inclusion of all
primes other than 3 and leaves the composite terms unclassified.

### Literature status

The source and literature screen recorded in #18591 cover the OEIS entry,
web searches for the sequence identifier and terms, GitHub Lean code,
`google-deepmind/formal-conjectures`, and `epoch-research/LeanOpenProblems`.
No earlier resolution was found in that searched scope. The source entry
states the assertion as a conjecture with a prime check below $10^6$.
The repository reuse search covers the sequence identifier, literal ratio
body, first-occurrence condition, and conclusion shape, including private
D5 declarations and pinned Mathlib. The mathematical component facts are
reused directly. This is not a certification of priority or exhaustive search.

## ASSUMED-UNVERIFIED

Completeness and currency of the literature screen, and absence of an earlier
published proof outside its searched scope, are unverified. The equality-case
candidate and composite classification are not delivered Lean results.
The escape audit remains unfinished under #19902; no `declared_validated`
registration is asserted.
