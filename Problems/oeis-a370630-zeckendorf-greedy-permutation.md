---
slug: oeis-a370630-zeckendorf-greedy-permutation
bibkey: oeis2024a370630
doi: null
url: https://oeis.org/A370630/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.result
---

# The one-common-Zeckendorf-term greedy sequence is a permutation

## Problem

This dossier anchors exactly the OEIS A370630 conjecture: “Conjecture: this
sequence is a permutation of the positive integers.” The record title is
“Lexicographically earliest sequence of distinct positive integers such that the
Zeckendorf expansions of two consecutive terms have exactly one common term.”
Rémy Sigrist is the record author; the conjecture comment has no separate signed
author. The source version is revision 16, revision time
2024-05-04T14:57:01-04:00, with offset 1,2.

Let F(0)=0, F(1)=1 and F(k+2)=F(k+1)+F(k). For every integer m>=1, let Z(m)
be its unique finite set of nonconsecutive indices k>=2 whose Fibonacci weights
sum to m. Set a(1)=1. At every integer n>=1, a(n+1) is the least integer m>=1
outside the actual prefix {a(1),...,a(n)} with |Z(m) intersect Z(a(n))|=1.
The whole assertion includes existence of an eligible unused successor at every
finite positive stage, distinctness at positive indices, and, for every m>=1,
a finite n>=1 with a(n)=m, all for that same sequence.

The linked PARI definition is https://oeis.org/A370630/a370630.gp.txt.
Its bit j encodes fibonacci(2+j); its candidate test is
`!seen(v) && hammingweight(bitand(zp, tozeck(v)))==1`.
Ordinary binary overlap, at-least-one overlap, zero overlap and finite checked
coverage are different assertions. The posted 1..10000 driver does not prove
the whole event.

## Motivation

The exact whole event is preregistered at
https://github.com/the-omega-institute/trureturing/issues/22916#issuecomment-6455424919.
The registration body SHA-256 is
`be4c48b37d89250e2d18945944f59181886adf667620d4fa4e5ddfea8a660c15`.
The canonical W-digit library supplies the representation interface; the
remaining question concerns totality and coverage of the actual least-unused
history, rather than existence of some permutation with a similar adjacency
condition.

## Gap

Canonical representation alone does not supply the next unused adjacent value
or show that no positive value is omitted forever. A finite prefix cannot
settle either unbounded obligation. The source record labels the permutation
assertion a conjecture; that label is a fact about this pinned record, not a
global openness or priority certificate.

## Route

A fresh sufficiently distant Fibonacci index pairs with an occupied current
index to give an eligible value larger than the sum of the used list. This
supplies every transition of a total recursion. The list-prefix invariant and
unused choice give injectivity.

If an omitted positive target has unbounded visited neighbors, numerical
minimality bounds each following value by that target, contradicting
injectivity. First appearances of arbitrarily large support indices force
visited canonical pairs. A two-successor comparison forces a pair rooted at
index two when the smaller index of such a pair is at least four. Finite
cutoffs yield an unbounded pair family rooted at some fixed index. Every
positive support containing that root is then visited. Fresh canonical triples
propagate this hub property to separated indices and supply unbounded visited
neighbors for every positive target.

## Falsifier

A missing eligible successor at a positive stage, a repeated value at distinct
positive indices, or a positive value absent from the same actual greedy
sequence would contradict the asserted event. Replacing the full prefix or
changing the exact-one canonical overlap condition would invalidate the source
correspondence even if a different theorem compiled.

## Evidence

The designated theorem is
`D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.result`, with closed
type `IsGreedyPermutation a`. Its five conjuncts express initial value,
positivity, actual successor eligibility and numerical leastness, injectivity
on positive indices, and attainment of every positive integer. The auxiliary
index zero is excluded from the event. The canonical support directly reuses
`D5.S0.Conventions.wdigits`, its canonicality, decoding and uniqueness.

The immutable source-byte identities are SHA-256
`cd97c6ba9e54e07a3508e12780155b3e5fa2cde74f4227cac025883597923c3a`
for the 1715-byte exact-ID JSON record and
`1f0281c622a920cade70aaf1767970c5b083e7561c54ec7cdbace4e14590c476`
for the 626-byte linked PARI definition. The URLs are mutable; these pins and
the revision identify the source evidence. The literal two-argument A000120
formula is disambiguated by the title and explicit bitand/hammingweight test.

Repository and pinned Mathlib searches found no exact whole supplier in their
searched scope. Two bounded GitHub Lean-code queries, `"Zeckendorf" "greedy" language:Lean` and `"A370630" language:Lean`, each returned zero indexed hits
on page one with per_page=30 and incomplete_results=false. The exact-ID
Crossref query returned total_results=0; OpenAlex returned HTTP 429 and provides
no negative supplier evidence. These are bounded searches, not an exhaustive
bibliography or absence-of-all-suppliers claim.

## Triage

### What the settlement shows

[proved, `D5/S3/Combinatorics/Permutation/ZeckendorfGreedyPermutation.result`]
The source sequence is total at every positive stage and permutes the positive
integers. The decisive mechanism is the combination of unbounded record pairs,
the two-successor forcing step, and propagation of the hub property by fresh
canonical triples. The proof uses actual numerical minimality and the full
history at every stage; it has no assumed infinitude or hub premise.

[open] Relaxing the starting value, changing the weight system or changing the
exact-one condition requires new correspondence and proof obligations. No
extension or sharp quantitative visitation bound is asserted. A226077 uses
ordinary binary terms, A332565 uses zero common Zeckendorf terms, and A370631
uses at least one common term; none is settled by this claim.

[open] No additional source result depending on this conjecture was identified
in the authenticated record and linked program. No consequences for an
unsearched paper, dependency chain or neighboring conjecture are certified.

## ASSUMED-UNVERIFIED

External source, registration and search evidence are inherited from the
completed source packet and bounded checks; this publication does not claim a
new comprehensive literature or owner census. Unindexed work, informal notes,
aliases and works lacking A370630 in indexed fields remain outside that search.
The record-author attribution does not authenticate a separate signature on
the conjecture comment. Source hashes authenticate bytes, not mathematical
truth, novelty or priority. No sequence program was executed for this result.
