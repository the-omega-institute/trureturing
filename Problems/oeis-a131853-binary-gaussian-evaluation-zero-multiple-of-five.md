---
slug: oeis-a131853-binary-gaussian-evaluation-zero-multiple-of-five
bibkey: zumkeller2007a131853
doi: null
url: https://oeis.org/A131853
triage: theorem
motivation_gids:
  - D5/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive
---

# Zeros of the A131853 binary Gaussian evaluation

## Problem

OEIS A131853, NAME (`%N`, verbatim):

> Numbers m such that z(m)=(0,0) with z as defined in A131851.

COMMENTS (`%C`, verbatim):

> Intersection of A131854 and A131855: A131851(a(n))=0, A131852(a(n))=0;

> conjecture: a(n) mod 5 = 0.

OEIS A131851, NAME (`%N`, verbatim):

> Real part of the function z(n)=Sum(d(k)*i^k: d as in n=Sum(d(k)*2^k), i=sqrt(-1)).

FORMULA (`%F`, verbatim):

> z(n) = if n=0 then (0, 0) else z(floor(n/2))*(0, 1) + (n mod 2, 0), complex multiplication.

The literal claim is `∀ m : ℕ, z m = 0 → 5 ∣ m`, where
`z : ℕ → GaussianInt` is defined by
`Nat.binaryRec 0 (fun b _ w => (if b then 1 else 0) + (⟨0, 1⟩ : GaussianInt) * w)`.
The Lean statement quantifies over every natural m, including zero.

## Motivation

Zumkeller recorded the conjecture in 2007. The formal result proves the full
unbounded divisibility statement for the binary Gaussian evaluation, rather
than only extending the displayed sequence of examples.

## Gap

The dated surfaces recorded in preregistration issue #7569 and its probe on
2026-09-13 were OEIS A131853 revisions 1–15: revision 1 introduced the
conjecture, and no later revision records a proof. A206715 asks whether it
duplicates A131853, A206716 gives a possibly equivalent integrality conjecture,
and A330714 only cross-references the entry. Exact-phrase arXiv search returned
0; OpenAlex and Crossref returned 0; MathOverflow and Stack Exchange returned
0. OEIS Open supplied only a metadata snapshot. The statement was absent from
epoch-research/LeanOpenProblems at
`bce747b3713f92678a68ca161b06356de5ff604e` and from
google-deepmind/formal-conjectures at
`786dd04e25528a354ffe929d659422921be15008`. Pinned Mathlib contained no
dominating theorem. These are bounded searches, and no priority is claimed;
the reduction is elementary.

## Route

Binary recursion gives `z(2n+b) = b + i·z(n)`. Modulo 5 the Gaussian unit
behaves like 2 because `2² ≡ −1`. Induction on the binary expansion therefore
gives `m ≡ Re z(m) + 2·Im z(m) (mod 5)`. If `z(m) = 0`, this invariant forces
`m ≡ 0 (mod 5)` and hence `5 ∣ m`.

## Falsifier

One natural m with `z(m) = 0` and `5 ∤ m` would refute the theorem.

## Evidence

- Lean module: `D5/S1/Digit/ZumkellerBinaryGaussianEvaluationZeroMultipleOfFive.lean`.
- Main theorem: `zumkeller_a131853`, with std3 axiom closure.
- The orchestrator checked `0 ≤ m ≤ 10⁶`: there were 59892 zeros of z; the
  first twelve were 0, 5, 10, 15, 20, 30, 40, 45, 60, 65, 75, and 80, matching
  `%S`; all were multiples of 5, with zero counterexamples, and the invariant
  was never violated.
- The independent probe recorded the same range, zero count, first twelve
  values, divisibility result, and invariant result.

## Triage

`theorem`

## ASSUMED-UNVERIFIED

The literature search is bounded. The arXiv and OpenAlex zero counts are the
dated issue/probe readings; this implementation's direct arXiv request did not
complete and its OpenAlex retry returned HTTP 429. No exhaustive-coverage or
priority claim is made.
