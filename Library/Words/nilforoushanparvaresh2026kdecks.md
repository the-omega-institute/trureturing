---
bibkey: nilforoushanparvaresh2026kdecks
authors: Arman Nilforoushan; Farzad Parvaresh
year: 2026
title: "Improved upper bound on the number of distinct k-decks for any k and alphabet size by counting the independent parameters"
doi: 10.48550/arXiv.2609.23106
url: https://arxiv.org/html/2609.23106v1
claim: "Conjecture 8.1: D_{q,k}(n) = Theta(n^{E_q(k)}) for every fixed q >= 2 and k >= 1, where E_q(k) = sum_{j=1}^k j L_q(j) - 1 and L_q(j) is the number of length-j Lyndon words over a q-letter alphabet."
strata_touched:
  - D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder
  - D5/S1/Words/Complexity/LyndonBrackets/LyndonStandardFactorization
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
and this note's source scope is its Conjecture 8.1.

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

The 32 formal owners are grouped into nine natural subdomains. The bracket and
fixed-source shuffle owners provide the triangular word-algebra machinery. The
positive-pair owners build actual positive words, retain duplicate indexed
family members, span the actual Lyndon directions, encode independent
multi-scale digits, and obtain a lower bound for the genuine cutoff-Magnus
image. The exact-deck owners transfer that construction to fixed-length exact
decks, recover every bounded scattered count from the actual Lyndon coordinates
without a guarded recovery hypothesis, and combine the lower and upper
estimates. These positive-word constructions and their complete composition
are repository results, not attributions to the cited paper.

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
different restricted converse for binomial complexity. Its definitions of
`scatteredCount` and `PositivePairIndex` are reused here, but its refutation is
not a proof of Conjecture 8.1 and is not counted as one.
