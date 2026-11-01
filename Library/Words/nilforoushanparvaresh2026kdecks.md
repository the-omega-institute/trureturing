---
bibkey: nilforoushanparvaresh2026kdecks
authors: Arman Nilforoushan; Farzad Parvaresh
year: 2026
title: "Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters"
doi: 10.48550/arXiv.2609.23106
url: https://arxiv.org/html/2609.23106v1
claim: "Conjecture 8.1: D_{q,k}(n) = Theta(n^{E_q(k)}) for every fixed q >= 2 and k >= 1, where E_q(k) = sum_{j=1}^k j L_q(j) - 1 and L_q(j) is the number of length-j Lyndon words over a q-letter alphabet. Lemma 4.4 states classical unique nonincreasing Lyndon factorization over a finite ordered alphabet."
strata_touched:
  - D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder
  - D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization
  - D5/S1/Words/Complexity/LyndonBrackets/LyndonFactorizationUnique
  - D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketAlgebra
  - D5/S1/Words/Complexity/LyndonBrackets/LyndonBracketLeading
  - D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleOrder
  - D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryScheduleEvaluation
  - D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryFrontPromotion
  - D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleOrder
  - D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedScheduleWeave
  - D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedSchedulePromotion
  - D5/S1/Words/Complexity/ShuffleOrders/Indexed/IndexedShuffleOrder
  - D5/S1/Words/Complexity/PositivePairs/Coefficients/CutoffCoefficientAlgebra
  - D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients
  - D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairFiltration
  - D5/S1/Words/Complexity/PositivePairs/Coefficients/PositivePairLeadingCoefficients
  - D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyHomogeneity
  - D5/S1/Words/Complexity/PositivePairs/Span/FullFamilyBracketSpan
  - D5/S1/Words/Complexity/PositivePairs/Span/LiteralPowerSubstitution
  - D5/S1/Words/Complexity/PositivePairs/Digits/ActualLyndonDirections
  - D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitWords
  - D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitData
  - D5/S1/Words/Complexity/PositivePairs/Digits/CentralDigitInjection
  - D5/S1/Words/Complexity/ExactDecks/Growth/PositiveWordBall
  - D5/S1/Words/Complexity/ExactDecks/Growth/PositivePairBallGrowth
  - D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckCore
  - D5/S1/Words/Complexity/ExactDecks/Growth/ExactDeckLowerBound
  - D5/S1/Words/Complexity/ExactDecks/UpperBound/OverlapInfiltration
  - D5/S1/Words/Complexity/ExactDecks/UpperBound/LyndonFactorization
  - D5/S1/Words/Complexity/ExactDecks/UpperBound/ShuffleScheduleComposition
  - D5/S1/Words/Complexity/ExactDecks/UpperBound/IteratedOverlapBounds
  - D5/S1/Words/Complexity/ExactDecks/UpperBound/FullLyndonRecovery
  - D5/S1/Words/Complexity/ExactDecks/Asymptotics/PositivePairExactDeckAsymptotics
license: citation-only
triage: anchor
---

# Exact k-deck asymptotics

## Verified locator

The verified locator is DOI `10.48550/arXiv.2609.23106` and canonical URL
`https://arxiv.org/html/2609.23106v1`. They identify version 1 of the cited paper,
and this note's source scope is its Conjecture 8.1 and the classical
factorization statement in Section 4, Lemma 4.4.

The cited source is arXiv:2609.23106v1, dated September 19, 2026. Its exact
title is *Improved upper bound on the number of distinct k-decks for any k and
alphabet size by counting the independent parameters*, by Arman Nilforoushan
and Farzad Parvaresh. The HTML source states the CC BY 4.0 license.

Conjecture 8.1 says, literally in its displayed formula and following
quantifier clause,

> D_{q,k}(n) = Theta(n^{E_q(k)}) for every fixed q >= 2, k >= 1.

Here `D_{q,k}(n)` is the number of distinct vectors of counts of all
length-`k` subsequences among words of length `n` over an alphabet of size
`q`, and

`E_q(k) = sum_{j=1}^k j L_q(j) - 1`,

where `L_q(j)` is the actual number of length-`j` Lyndon words over that
alphabet. The source proves the matching upper bound for every `q,k`, proves
the lower bound for `k=2` and every `q`, and proves the case `q=2,k=3`; it
explicitly leaves the general matching lower bound open.

## Source context

The paper identifies its subsequence-count product rule with the infiltration
product of Chen, Fox and Lyndon, and identifies the top-degree part with the
shuffle product. It cites Chen-Fox-Lyndon factorization, Radford's shuffle
algebra theorem, Lothaire's *Combinatorics on Words*, and Reutenauer's *Free
Lie Algebras* for the classical Lyndon and shuffle background. Those classical
facts are source context; this repository does not claim to have discovered
them.

The 33 formal owners are grouped into nine natural subdomains. The bracket and
fixed-source shuffle owners provide the triangular word-algebra machinery. The
positive-pair owners build actual positive words, retain duplicate indexed
family members, span the actual Lyndon directions, encode independent
multi-scale digits, and obtain a lower bound for the genuine cutoff-Magnus
image. The exact-deck owners transfer that construction to fixed-length exact
decks, recover every bounded scattered count from the actual Lyndon coordinates
without a guarded recovery hypothesis, and combine the lower and upper
estimates. These positive-word constructions and their complete composition
are repository results, not attributions to the cited paper.

## Classical Lyndon factorization

Section 2 fixes a finite totally ordered alphabet
`A = {a_1 < a_2 < ... < a_q}`. Definition 4.1 calls a nonempty word Lyndon
when it is strictly smaller in lexicographic order than each nontrivial
rotation. Lemma 4.4, headed Chen–Fox–Lyndon, states that every nonempty word
has a unique factorization `w = l_1 ... l_r` into Lyndon words with
`l_1 >= ... >= l_r`. Repeated factors are allowed. This is classical
background, not a new theorem of the cited paper. Its bibliography lists
Chen, Fox and Lyndon's original article and Lothaire's textbook; the
attribution here is to the statement in Lemma 4.4, not to a direct
inspection of those earlier works.

The formal uniqueness theorem allows any linearly ordered alphabet.
This scope is obtained from the finite-alphabet statement by a
finite-support transfer, not by attributing an infinite-alphabet statement
to the paper. For two factorizations of the same finite word `w`, every
letter of every factor lies in the finite set `B` of letters in `w`.
The inherited order makes `B` a finite linear order, and its increasing
rank map is an order isomorphism to a finite chain. On words supported in
`B`, this relabeling preserves and reflects equality and lexicographic
comparison, including comparisons decided by a proper prefix. It
commutes with concatenation, splitting and rotation. Hence it preserves
and reflects both the rotation-based Lyndon predicate and nonincrease.
Apply Lemma 4.4 to the relabeled word and use injectivity to recover
equality of the original lists. Unused letters may be added to the finite
chain if at least two alphabet symbols are required. The empty word is
handled separately: since each Lyndon factor is nonempty, both factor
lists must be empty. No finiteness, well-ordering or discreteness
assumption on the ambient alphabet is needed. The Lean proof works
directly over that ambient linear order; this transfer explains the
literature scope and is not an additional formal premise.

## Bounded later-source check

On September 24, 2026, the exact arXiv HTML source still presented the general
statement as Conjecture 8.1. OpenAlex identified the same arXiv work and
reported `cited_by_count = 0`. Crossref exact-title search returned no matching
later work among its first three results. Semantic Scholar returned HTTP 429,
so that surface is `ASSUMED-UNVERIFIED`. These are bounded checks only. They do
not establish worldwide absence, historical priority, or absence of a proof
outside the searched sources.

The earlier frozen
`D5/S1/Words/Complexity/VivionBinomialConverseFails` theorem concerns a
different restricted converse for binomial complexity. Its definition of
`scatteredCount` is reused here. `PositivePairIndex` is newly declared in
`PositivePairFiltration`; the frozen refutation is not a proof of Conjecture 8.1.
