---
slug: oeis-a006972-rotondo-lucas-carmichael-sufficient-condition
bibkey: rotondo2020a006972
doi: null
url: https://oeis.org/A006972
triage: theorem
motivation_gids:
  - D5/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion
---

# Rotondo's A006972 Lucas-Carmichael sufficient condition

## Problem

OEIS A006972, NAME (`%N`, verbatim):

> Lucas-Carmichael numbers: squarefree composite numbers k such that p | k => p+1 | k+1.

Davide Rotondo's COMMENT (`%C`, verbatim) is:

> Conjecture: if k = p*q*r, p = a*d - 1, q = b*d - 1, r = c*d - 1 are distinct odd primes, with d = gcd(p + 1, q + 1, r + 1) and a*b*c*d divides k + 1, then k is a Lucas-Carmichael number. - _Davide Rotondo_, Dec 23 2020

The full-quantifier reading takes `a,b,c,d,p,q,r,k` in the natural numbers,
keeps the stated positivity, odd-prime, distinctness, product, gcd, and
divisibility hypotheses, and concludes that `k` is squarefree, composite,
greater than one, and satisfies `s+1 | k+1` for every prime divisor `s`.
The equations `p+1=a*d`, `q+1=b*d`, and `r+1=c*d` are equivalent to the
source's subtraction equations under the corresponding prime hypotheses:
primality gives positivity, which removes the natural-subtraction truncation.

## Motivation

The independent question is Rotondo's named sufficient condition for a
three-prime product to be Lucas-Carmichael. Issue #8377 registered the exact
quantifiers and delivery surface before the proof probe.

## Gap

Reading dated 2026-09-17: the OEIS entry still labels the sentence
`Conjecture`, has no `%F` line, and carries no settlement marker. Every paper
linked from the entry's `%H` lines was read after download and conversion;
the corresponding Wikipedia and MathWorld pages were also searched. No proof
or refutation of this criterion was found in those sources.

Repository searches at `origin/dev` found no `A006972`, `LucasCarmichael`,
`Lucas-Carmichael`, module-name, or exact-conclusion-shape match in D5,
Blueprint, Library, Problems, or Meta. The three `Rotondo` matches concern a
continued-fraction bibliography, and the `Korselt` matches state the distinct
`p-1 | n-1` condition. Pinned Mathlib has no Lucas-Carmichael predicate or
statement of this criterion.

The theorem has `proof_shape: bind-only`, `escape_witness: none`, and
`admission_basis: open-problem-resolution`. It has no direct frozen repository
dependencies; all mathematical prerequisites are from pinned Mathlib. The
utility classification is `none`: the definition and theorem are unbounded
symbolic mathematics, not bounded enumeration, checker infrastructure,
numeric reduction, or a certified finite instance.

## Route

1. Distinct primality makes `p*q*r` squarefree and makes the product composite
   and greater than one.
2. Every prime divisor of `p*q*r` equals one of `p`, `q`, or `r`.
3. In each case, the matching equation makes its successor divide `a*b*c*d`,
   which divides `k+1` by hypothesis.

## Falsifier

Natural numbers satisfying all displayed hypotheses while the product is not
squarefree, is prime, is at most one, or has a prime divisor whose successor
does not divide `k+1` would falsify the theorem. The concrete tuple
`(a,b,c,d,p,q,r,k)=(1,2,5,4,3,7,19,399)` inhabits all hypotheses.

## Evidence

- Final Lean module:
  `D5/S3/Arith/Congruence/RotondoLucasCarmichaelCriterion.lean`.
- `make lean` and `make lean-report` on the final source exit 0.
- `#print axioms result` exits 0 with exactly
  `[propext, Classical.choice, Quot.sound]`.
- Deleting the sole direct import, `Mathlib.Data.Nat.Squarefree`, makes
  `make lean` exit 2.
- A pinned-toolchain Lean probe checks the displayed tuple and the equivalence
  `p = x-1 <-> p+1=x` under `Nat.Prime p`.

## Triage

`theorem`; resolution `proved` for Rotondo's A006972 sufficient-condition
sentence. The Scribe theorem node carries the matching
`OpenProblemResolutionClaim` with `ResolutionKind.Proved`.

## ASSUMED-UNVERIFIED

Historical openness beyond the OEIS-linked papers, Wikipedia, and MathWorld
surfaces described above is unverified. No exhaustive global novelty or
priority claim is made beyond those sources.
