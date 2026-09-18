---
slug: fazekas-abelian-square-equality-refutation
bibkey: fazekas2026binary
doi: 10.48550/arXiv.2604.23188
url: https://arxiv.org/abs/2604.23188v1
triage: theorem
motivation_gids:
  - D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.result
---

# Refutation of the equality conclusion in Fazekas et al. Conjecture 4

## Problem

Conjecture 4 of Fazekas, Mammoliti, Mercaş, and Simpson,
*Binary Words Containing Few Abelian Squares*, arXiv:2604.23188v1,
states that every binary word of length n contains at least floor(n/4)
distinct abelian-square factors and that equality forces all of those factors
to be trivial even powers of one letter.

The formal claim quantifies over every finite binary word, counts distinct
factors whose equal-length halves have the same Parikh vector, and expresses
both the lower bound and the equality conclusion.

## Motivation

The kernel-checked word `abab` has length 4 and exactly one distinct
abelian-square factor, namely `abab`. Thus its count equals floor(4/4), while
the factor uses both letters and is not a positive even power of either one.
The equality conclusion, and hence the published conjunction, is false.

## Gap

The result refutes only the equality conclusion of the literal Conjecture 4.
It does not refute the floor(n/4) lower bound or assert a corrected equality
classification.

## Route

Represent the binary alphabet by `Bool` and distinct factors by a filtered
finite set of prefixes of suffixes. Finite reduction verifies the factor set
and the equality count at `abab`; specializing the conjecture then forces the
mixed-letter factor to be a constant-letter even power, a contradiction.

## Falsifier

A proof that every binary word attaining the floor(n/4) bound has only
constant-letter even-power abelian squares would contradict
`D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.result`.

## Evidence

- Lean module: `D5/S1/Words/Powers/FazekasAbelianSquareEqualityRefutation.lean`.
- Resolution theorem: `result : Not claim`.
- The typed utility evidence identifies `result` as the closed negation of
  `claim`.
- Literature source: DOI `10.48550/arXiv.2604.23188`, arXiv version 1.

## Triage

`theorem`; resolution `refuted` for the literal Conjecture 4 statement. The
counterexample settles the conjunction through its equality clause only.

## ASSUMED-UNVERIFIED

The mapping from the paper's natural-language definitions to the Lean
encoding is a source-faithfulness judgment, not a kernel theorem. The
literature search recorded in issue #8589 was bounded to the cited arXiv
version, repository records, and arXiv search. Semantic Scholar and Google
Scholar were not verified; exhaustive coverage and publication priority
remain unverified.
