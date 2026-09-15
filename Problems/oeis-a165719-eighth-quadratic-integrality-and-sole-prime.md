---
slug: oeis-a165719-eighth-quadratic-integrality-and-sole-prime
bibkey: orlovsky2009a165719
doi: null
url: https://oeis.org/A165719
triage: theorem
motivation_gids:
  - D5/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime.result
---

# A165719 integrality and the sole prime

## Problem

The OEIS entry states, verbatim:

> %N A165719 Integers of the form k*(k+9)/8.
> %C A165719 Only one term is a prime number (17). Are all others composite?
> %F A165719 Conjecture: Valid k values are pairs of the form (8*m-1,8*m) for m=1,2,3.... If true, 17 is the only prime term. - _Bill McEachen_, May 06 2026
> %A A165719 _Vladimir Joseph Stephan Orlovsky_, Sep 24 2009
> %O A165719 1,1

For every positive natural k, `8 | k*(k+9)` is equivalent to the existence
of a positive natural m with `k+1=8*m` or `k=8*m`. A natural a is an
integral term exactly when some positive k satisfies `8*a=k*(k+9)`.
The value 17 is a term and a prime; every other term is greater than one
and not prime. The example's positive-parameter restriction is retained.
The equations avoid natural-number floor division and truncated subtraction.

Not claimed: a result for nonpositive parameters, a new method of prime
classification, any assertion about arbitrary quadratic forms, an
exhaustive literature search, or priority beyond the settlement of these
named assertions in the searched scope.

## Motivation

Orlovsky submitted the sequence in September 2009. The sole-prime question
is present in archived revision #1 (June 1 2010), and McEachen's parameter
conjecture was added on May 6 2026. The proof is elementary; the novelty is
the settlement of the named assertions, not the technique.

## Gap

Revision #24 (May 14 2026 00:56:29) still carries both assertions without
a settlement comment or proof link. There is no `%D` bibliography; its
only `%H` is an internal linear-recurrence index. Dale's first-million-term
check is finite evidence, not a universal proof. Repository and pinned
Mathlib statement-shape searches, online Loogle queries for the divisibility
and prime-product shapes, and GitHub Lean-code searches returned no exact
settlement. The preregistration's bounded external web search also found no
settlement. This is `not-found-in-searched-scope`, not an exhaustive claim.

## Route

Reduction modulo eight shows that only residues zero and seven make the
product divisible by eight. If `k+1=8*m`, cancellation gives `a=k*(m+1)`;
both factors exceed one. If `k=8*m`, cancellation gives `a=m*(8*m+9)`.
The case m=1 gives 17; every other positive m makes both factors exceed one.
The universal conclusion follows from product bounds and nonprimality of
a product whose factors differ from one.

## Falsifier

A positive parameter with an integral value but residue outside zero and
seven modulo eight, or a prime integral term different from 17, would
contradict the respective conjunct of `result`.

## Evidence

The Lean module is `D5/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime.lean`.
Its single theorem contains the full parameter classification, the prime
term 17, and the composite characterization of every other term.
The proof uses Mathlib's modular arithmetic, product bounds, cancellation,
and `Nat.not_prime_mul`; it introduces no additional mathematical assumption.

## Triage

`theorem`: both named assertions are proved for all positive natural
parameters and all integral terms, not just a bounded initial segment.
The resolution kind is `proved`, not `refuted`.

## ASSUMED-UNVERIFIED

Literature completeness outside the named searches is unverified. Google
Scholar and MathSciNet were not searched; no exhaustive literature or
priority claim is made. The preregistration's web and revision-history
readings are attributed to the orchestrator; the current OEIS text and
Lean-library searches were independently checked by the implementation seat.
