---
slug: oeis-a116184-generalized-harmonic-thirty-seven-cube-progression
bibkey: adamchuk2007a116184
doi: null
url: https://oeis.org/A116184
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression
---

# Cubic divisibility of generalized harmonic numerators along Adamchuk's progression

## Problem

OEIS A116184, NAME (`%N`, verbatim):

> Numbers n such that 37^3 divides the numerator of generalized harmonic number H(36,n) = Sum[ 1/k^n, {k,1,36} ].

COMMENT (`%C`, verbatim):

> Conjecture: All terms of the arithmetic progression 3+36k belong to a(n).

AUTHOR (`%A`, verbatim):

> _Alexander Adamchuk_, Apr 08 2007

The first terms (`%S`) are:

> 3, 37, 39, 73, 75, 111, 147, 148, 183, 185, …

The literal claim is `∀ k ∈ ℕ, 37³ ∣ num(H(36, 3+36k))`, where `Rat.num`
is the reduced numerator.
The same OEIS comment also discusses primes of the form `37m-1` and cases of
divisibility by `37^4`; neither assertion is claimed here.

## Motivation

The comment singles out an infinite arithmetic progression inside the sequence.
A universal proof settles every term of that progression rather than extending
the finite list of verified exponents.

## Gap

The surfaces recorded in preregistration issue #7581 and its probe were checked
on 2026-09-13. The OEIS entry had six revisions: the conjecture was unchanged
from revision 2 onward, and the later revisions changed only keywords, formatting,
or links. OEIS Open arXiv:2608.11941, `epoch-research/LeanOpenProblems`, and
`google-deepmind/formal-conjectures` did not contain this problem. Exact-phrase
arXiv searches returned 0 results, and MathOverflow searches returned 0 results.
OpenAlex returned HTTP 429, so its result is `ASSUMED-UNVERIFIED`.

The search seat reported that the case `k=0` followed from Zhao Theorem 2.8 or
Gy Theorem 3.2 together with the irregular pair `(37,32)`. The probe could not
identify those references, and arXiv:math/0303332v3 has no Theorem 2.8. That
literature report is `ASSUMED-UNVERIFIED` and is not used. Wolstenholme-type
congruences of generalized harmonic numbers are classical; no priority claim is
made for the progression or its proof.

## Route

Let `L=36!`, `b_j=L/j`, and `N(n)=Sum_j b_j^n`, so that
`H(n)=N(n)/L^n`. In `ZMod(37^3)`, Fermat gives
`37 | b_j^36-1`, hence `(b_j^36-1)^3=0`. Therefore
`C_k=Sum_j b_j^3*(b_j^36)^k` satisfies
`C_(k+3)-3*C_(k+2)+3*C_(k+1)-C_k=0`. Finite certificates establish
`C_0=C_1=C_2=0`, and strong induction gives `C_k=0` for every natural k.

For the numerator bridge, `den(H(n)) | L^n`, and `L^n` is coprime to 37.
The identity `num(H(n))*L^n=N(n)*den(H(n))` transfers divisibility by
`37^3` from `N(3+36k)` to the reduced numerator.

## Falsifier

One natural k for which `37^3` does not divide the reduced numerator of
`H(36,3+36k)` would contradict the theorem.

## Evidence

- Lean module: `D5/S3/ArithSums/AdamchukGeneralizedHarmonicThirtySevenCubeProgression.lean`.
- Main theorem: `adamchuk_a116184`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`).
- The orchestrator checked `N(3+36k) = 0 (mod 37^3)` for `0 <= k < 400`
  and exact rational values for `k=0,1,2,3`.
- The orchestrator found that
  `{1 <= n < 340 : 37^3 | num(H(36,n))}` equals the displayed `%S` terms
  in that range.
- With `r_j=b_j^36`, the orchestrator checked `r_j = 1 (mod 37)`,
  `(r_j-1)^3 = 0 (mod 37^3)`, and `C_0=C_1=C_2=0`.
- The independent probe recorded the same modular, rational, sequence, and
  certificate readings before proving the universal statement.

## Triage

`theorem`. The formal result proves the full arithmetic progression for every
natural k.

## ASSUMED-UNVERIFIED

OpenAlex completeness was not checked because the service returned HTTP 429.
The search seat's Zhao/Gy citation could not be identified and is not relied
upon. All search results are bounded to the named surfaces and date; they do not
establish exhaustive literature coverage or publication priority.
