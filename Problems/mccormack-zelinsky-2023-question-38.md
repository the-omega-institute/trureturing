---
slug: mccormack-zelinsky-2023-question-38
bibkey: mccormackzelinsky2023weightedamgm
doi: 10.48550/arXiv.2312.11661
url: https://arxiv.org/abs/2312.11661v4
triage: theorem
motivation_gids:
  - D5/S3/Arith/Abundancy/McCormackZelinskyQuestion38.result
---

# Sixty times every power of two is strongly pseudoperfect

## Problem

McCormack and Zelinsky, arXiv:2312.11661v4, page 17:

> Question 38. For any n ≥ 0, is 60(2^n) strongly pseudoperfect?

A positive integer N is strongly pseudoperfect when a subset S of its positive
divisors satisfies d∈S if and only if N/d∈S, for every positive divisor d,
and the sum of S is 2N. The set may contain N. The formal statement uses
`StrongPseudoperfectDensity.StronglyPseudoperfect` without changing this definition.
The source exponent n corresponds to the natural number j in `result`.

## Motivation

The question asks for an entire family with fixed odd part 15 and every
2-adic valuation at least two. Producing isolated strongly pseudoperfect
multiples does not settle these quantifiers.

## Gap

An admissible divisor sum must satisfy both exact mass and complementary
closure. The same chosen subset must satisfy both conditions for every exponent;
independent constructions of a subset of the right mass and a complementary
subset do not suffice.

## Route

Write a=j+2, so N=15·2^a. Coprimality gives unique divisor coordinates
2^i d with 0≤i≤a and d∈{1,3,5,15}. For a≥5 choose the following layers:

| Exponent i | Chosen odd parts d |
| --- | --- |
| 0 and a | 1,15 |
| 1 and a−1 | 1,3,5,15 |
| 2 and a−2 | none |
| 3≤i≤a−3 | 3,5 |

Complementation is (i,d)↦(a−i,15/d). Every row's exponent set and odd-part
set are stable under these maps. The chosen products are distinct and divide N.
The sum is

$$
16(1+2^a)+24(2+2^{a-1})+8\sum_{i=3}^{a-3}2^i
=16(1+2^a)+24(2+2^{a-1})+8(2^{a-2}-8)
=30\cdot2^a=2N.
$$

The middle sum is empty for a=5. For a=2,3,4 take all divisors except,
respectively,

$$
\{2,30,6,10\},\quad
\{3,40,5,24,6,20,10,12\},\quad
\{2,120,4,60,6,40,12,20\}.
$$

These omitted sets are unions of complementary pairs, and the remaining
sums are 120,240,480. The same definition of strong pseudoperfection applies
to the three base cases and the infinite construction.

## Falsifier

The exponent zero must be included. Replacing strong pseudoperfection by
an arbitrary divisor sum, counting products with multiplicity, omitting the
closure implication in either direction, or replacing the sum 2N by N would
change the question. Empty middle layers at a=5 require no exceptional limit
argument; a=2,3,4 use separate exact sets.

## Evidence

`D5/S3/Arith/Abundancy/McCormackZelinskyQuestion38.result` has statement
`∀ j : ℕ, StronglyPseudoperfect (60 * 2 ^ j)`.
Its `OpenProblemResolutionClaim` is **Proved**. The external settlement is
preregistered in #31869. The proof uses the existing strongly pseudoperfect
predicate and pinned Mathlib's coprime divisor-product injectivity and
geometric-sum identity.

Bounded literature check supplied with the problem: arXiv:2312.11661v4
still lists Question 38 as a question on page 17. Wang–Zelinsky's Theorem 5
on power lifting does not cover the fixed odd part 15 with arbitrary
2-adic valuation. The supplied searches of subsequent preprints and public
repositories found no all-exponent answer. These external searches were not
independently repeated in the offline environment. Global priority is unverified.

## Triage

### What the settlement shows

- **Proved:** `result` answers Question 38 affirmatively for every j≥0.
  The mechanism is a symmetric choice of binary layers, with odd-part
  sums 16,24,0,8. The geometric middle contribution cancels the constant
  boundary contribution exactly. The construction proves existence; it
  does not classify all admissible divisor subsets.
- **Computed:** exact integer checks for a=5,…,199 passed at all 195
  exponents. The constructed sets have 2a+2 elements, no duplicate
  products, complementary closure and sum 30·2^a. The smaller cases
  a=2,3,4 have respectively 12,16,20 divisors and selected cardinalities
  8,8,12, with sums 120,240,480. These finite readings are checks of the
  construction; the unrestricted statement is the theorem above.
- **Proved (arithmetic consequence, not a separate Lean declaration):**
  an odd part m supporting every sufficiently large exponent must satisfy
  3∣m, as observed in the source discussion. If 3∤m, arbitrarily large
  a give m·2^a≡2 modulo 3. Then there are no self-complementary divisors,
  and every complementary pair has sum zero modulo 3. A closed divisor
  subset cannot have sum 2m·2^a, which is nonzero modulo 3.
- **Computed:** exhaustive subset-sum on complementary-pair weights for
  0≤a≤10 gives the following passing exponents for m·2^a. Square-root
  divisors, when present, are counted once.

  | Odd part m | Passing a in 0,…,10 |
  | --- | --- |
  | 3 | 1 |
  | 9 | 2,6,7,8,9,10 |
  | 15 | 2,3,4,5,6,7,8,9,10 |
  | 21 | 2,4,5,6,7,8,9,10 |
  | 27 | 3,5,6,7,8,9,10 |
  | 33 | 5,6,7,8,9,10 |
  | 39 | 2,3,4,5,6,7,8,9,10 |
  | 45 | 1,4,5,6,7,8,9,10 |

  The calculation enumerates odd divisors d∣m and levels 0≤i≤a,
  forms each complementary orbit's sum w, and updates the exact bitset
  B↦B OR (B shifted left by w), starting with B=1 and truncating above
  2m·2^a. The target bit is the existence test. There are 88 tested
  pairs (m,a); no claim about larger exponents follows from this table.
  In particular, neither 15 nor 30 is strongly pseudoperfect, whereas the
  proved family starts at 60: the initial exponent a=2 cannot be lowered.
- **Open:** classify odd m for which all sufficiently large m·2^a are
  strongly pseudoperfect, or for which the property holds from a specified
  initial exponent. The necessity 3∣m alone is not a sufficient condition
  established here. A construction for odd parts other than 15 needs
  compatible divisor-complement orbits and new boundary mass equations;
  the numerical tails above do not prove such an extension.
- **Open (source dependency boundary):** no original-paper theorem
  conditional on Question 38 is identified in the supplied source excerpt.
  This settlement establishes the requested infinite even family. It
  does not resolve the classification of other odd parts, strengthen the
  source's density questions, or change their independently proved results.

## ASSUMED-UNVERIFIED

Worldwide priority, exhaustive later literature coverage, the full wording
and hypotheses of Wang–Zelinsky Theorem 5, and a complete dependency scan of
the original paper are not independently verified offline. The bounded
literature findings above are attributed to the supplied review. The formal
all-exponent statement does not depend on those bibliographical assumptions.
