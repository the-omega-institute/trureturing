---
slug: chauve-zhang-unary-neighborhood-minimality
bibkey: chauve2025neighborhoods
doi: 10.48550/arXiv.2505.13796
url: https://arxiv.org/abs/2505.13796v2
triage: theorem
motivation_gids:
  - D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed
---

# Chauve--Zhang unary neighborhood minimality

## Problem

Chauve and Zhang, *On the size of the neighborhoods of a word*,
arXiv:2505.13796v2, Section 6, printed page 7, ask whether unary words have
the smallest condensed or super condensed neighborhoods among words of the
same length over a fixed alphabet.

For a word `w` and radius `d`, Equations (2.1)--(2.3) define `N(w,d)` as the
words at Levenshtein distance at most `d`, `CN(w,d)` as the members of
`N(w,d)` with no proper prefix in `N(w,d)`, and `SCN(w,d)` as the members with
no proper contiguous subword in `N(w,d)`. Thus the question asks whether,
for every finite alphabet, length `n`, radius `d`, letter `a`, and word `w`
of length `n`,

- `|CN(a^n,d)| <= |CN(w,d)|`, and
- `|SCN(a^n,d)| <= |SCN(w,d)|`.

## Motivation

The paper proves exact cardinality formulas for the condensed and super
condensed neighborhoods of unary words. The closing question asks whether
those values are lower bounds for arbitrary words, extending the known
minimality of unary words for whole Levenshtein neighborhoods.

## Gap

Version 2 retains the closing question. The bounded literature check recorded
in issue #8618 covered the arXiv version history, exact topic searches, the
paper's cited whole-neighborhood result, and the available Semantic Scholar
citation data. It found no proof or refutation of either assertion in that
scope. Google Scholar and exhaustive worldwide literature were not checked.

## Route

Use the binary alphabet. At length three and radius two,
`CN(000,2) = {0,10,110}` while `CN(001,2) = {0,1}`. Hence the proposed
condensed inequality specializes to `3 <= 2`.

At length four and radius one, `SCN(0000,1) = {000,0010,0100}` while
`SCN(0011,1) = {001,011}`. Hence the proposed super condensed inequality
also specializes to `3 <= 2`.

The source-form distance is the infimum of alignment costs. The public
identity `levenshtein_eq_dlev` proves that the executable Wagner--Fischer
recurrence computes this distance, so both finite neighborhood calculations
apply to the paper's stated metric.

## Falsifier

Either route would fail if its displayed neighborhood enumeration were
incorrect under the minimum-alignment-cost definition. A failure of
`levenshtein_eq_dlev`, or a proof that either displayed three-element set has
cardinality at most the corresponding two-element set, would also invalidate
the relevant refutation.

## Evidence

- Frozen identity:
  `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.levenshtein_eq_dlev`.
- Frozen condensed refutation:
  `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed`.
- Frozen super condensed refutation:
  `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultSuperCondensed`.
- The formal claims quantify the alphabet, length, radius, unary letter, and
  comparison word, and retain the source's unrestricted radius.

## Triage

`theorem`; resolution `refuted`. The identity and both refutations have
`proof_shape: content`. The identity has `admission_basis: escape-witness`;
the two published-question refutations have
`admission_basis: open-problem-resolution` under preregistration #8618.

## ASSUMED-UNVERIFIED

The literature review is bounded and does not establish exhaustive absence
of corrections, unpublished work, paywalled citing papers, or unindexed
resolutions. No worldwide novelty or publication-priority claim is made.
