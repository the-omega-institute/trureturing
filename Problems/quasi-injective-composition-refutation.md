---
slug: quasi-injective-composition-refutation
bibkey: pongsriiam2021quasi
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL24/Pongsriiam/pong23.pdf
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.result
---

# Quasi-Injective Composition Refutation

## Problem

Pongsriiam, *Journal of Integer Sequences* 24 (2021), Article 21.10.1,
Definition 1, reads: "We call a function `f : N → C` a quasi-injective function
if for all `a, b ∈ N`, the condition `f(an) = f(bn)` for all `n ∈ N` implies
`a = b`." Section 5 asks:

> Question 19. Suppose `f` and `g` are quasi-injective. Is the composition
> `f ∘ g` quasi-injective?

The same item goes on to ask for a classification of the pairs whose composite is
quasi-injective, and records that "An obvious sufficient condition for `f ∘ g` to
be quasi-injective is that `g` is both surjective and completely multiplicative,
but there may be a weaker condition." Only the displayed question is settled here.

## Motivation

The frozen theorem
`D5/S3/Combinatorics/QuasiInjectiveCompositionRefutation.result` answers it in
the negative by an explicit pair. Quasi-injectivity is therefore not preserved by
composition, so the classification the article asks for is not vacuous: the
sufficient condition it names cannot be dropped entirely.

## Gap

The journal article and its HTML record were opened; the author's publication
page lists this as his only item on quasi-injectivity and shows no follow-up; the
one citing paper in the screened corpus, Pongsriiam, *J. Integer Seq.* 26 (2023),
Article 23.9.1, cites it only in the reference list. Web search for
"quasi-injective" in this arithmetic sense returns only this article.
Citation-index result pages were not reachable, so this is a bounded negative
finding.

## Route

Take

    g(n) = n^2 ,
    f(n) = 1 if n is a perfect square, and f(n) = n otherwise.

`g` is quasi-injective: if `g(an) = g(bn)` for every `n`, then already `n = 1`
gives `a^2 = b^2`, hence `a = b`.

`f` is quasi-injective: let `a ≠ b` be positive and choose a prime `p > ab`,
which exists because the primes are unbounded. Then `p ∤ a` and `p ∤ b`. If
`ap = k^2` then `p ∣ k·k`, so `p ∣ k`, so `p^2 ∣ ap` and therefore `p ∣ a`, a
contradiction; so `ap` is not a perfect square, and neither is `bp`. Hence
`f(ap) = ap ≠ bp = f(bp)`, and the multiplier `n = p` separates `a` from `b`.

`f ∘ g` is not quasi-injective: `f(g(n)) = f(n^2) = 1` for every `n`, so with
`a = 1` and `b = 2` the composite agrees on all multiples while `1 ≠ 2`.

Note that `g` is completely multiplicative but not surjective, so the
counterexample does not contradict the sufficient condition the article names.

## Falsifier

A pair `a ≠ b` for which `f(an) = f(bn)` holds for every `n` would invalidate the
outer factor; the prime recipe above is the sharpest test, since it produces an
explicit separating multiplier for each pair. Replacing "perfect square" by a
property that multiplication preserves breaks the construction: collapsing the
multiples of four instead leaves `a = 4` and `b = 8` inseparable, because `4 ∣ an`
and `4 ∣ bn` for every `n`.

## Evidence

An independent implementation confirms `f(g(n)) = 1` for `n ≤ 20`, that every one
of the 1770 pairs `a < b ≤ 60` is separated by some `n < 400`, and that the
explicit recipe "take the least prime not dividing `ab`" yields, for every one of
those pairs, multipliers with `ap` and `bp` non-square and `f(ap) ≠ f(bp)`. There
were no mismatches. This is a check of the pair, not of the theorem: the theorem
is proved for all positive `a` and `b`.

## Triage

`theorem`; Tier 1 named external open question, preregistered in issue 9308
before implementation. The admission basis is `open-problem-resolution`. The
classification is `proof_shape: content`; the escape content is that a positive
integer multiplied by a prime not dividing it is never a perfect square, together
with the quasi-injectivity of the collapsing function, whose proof rests on that
fact and on the unboundedness of the primes. The computational use is a
`certified-instance` with a typed `refutes` edge from `result` to `claim`.

## ASSUMED-UNVERIFIED

The literature screen is bounded: the journal article and its HTML record, the
author's publication page, and the one citing paper in the screened corpus were
opened; citation-index result pages were not reachable, so no worldwide priority
claim is made.

The remainder of Question 19, which asks for a classification of the pairs whose
composite is quasi-injective and for a condition weaker than "`g` surjective and
completely multiplicative", is not settled here. Questions 16, 17 and 18 of the
article are separate; Question 17 is settled in
`D5/S3/Combinatorics/QuasiInjectiveOrderSeparation`.

The pair exhibited here is one counterexample and is not claimed to be minimal or
canonical; in particular no pair of the classical arithmetic functions studied in
the article is shown to have this behaviour.
