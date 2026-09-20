---
slug: chauve-zhang-super-condensed-neighborhood-unary-minimality
bibkey: chauve2025neighborhoods
doi: 10.48550/arXiv.2505.13796
url: https://arxiv.org/abs/2505.13796v2
triage: theorem
motivation_gids:
  - D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultSuperCondensed
---

# Chauve--Zhang super-condensed-neighborhood unary minimality

## Problem

Chauve and Zhang, *On the size of the neighborhoods of a word*,
arXiv:2505.13796v2, Section 6, printed page 7, ask:

> It was also shown in [6] that unary words have the smallest neighborhoods
> among all words of the same length over a given alphabet, thus leading to
> lower bounds for the size of neighborhoods. It is thus natural to ask if a
> similar property holds for condensed and super condensed neighborhoods,
> namely that unary words have the smallest condensed or super condensed
> neighborhoods.

This dossier tracks the super-condensed assertion. Equations (2.1) and (2.3)
define `N(w,d)` as the words at Levenshtein distance at most `d` and
`SCN(w,d)` as the members of `N(w,d)` with no proper contiguous subword in
`N(w,d)`. The assertion asks whether, for every finite alphabet, length `n`,
radius `d`, letter `a`, and word `w` of length `n`,

`|SCN(a^n,d)| <= |SCN(w,d)|`.

## Motivation

The paper proves exact cardinality formulas for super-condensed neighborhoods
of unary words. The closing question asks whether those values are lower
bounds for arbitrary words, extending the known minimality of unary words for
whole Levenshtein neighborhoods.

## Gap

Version 2 retains the closing question. The bounded literature check recorded
in issue #8618 covered the arXiv version history, exact topic searches, the
paper's cited whole-neighborhood result, and the available Semantic Scholar
citation data. It found no proof or refutation of the super-condensed
assertion in that scope. Google Scholar and exhaustive worldwide literature
were not checked.

## Route

Use the binary alphabet. At length four and radius one,
`SCN(0000,1) = {000,0010,0100}` while `SCN(0011,1) = {001,011}`. Hence the
proposed super-condensed inequality specializes to `3 <= 2` and is refuted.

The source-form distance is the infimum of alignment costs. The public
identity `levenshtein_eq_dlev` proves that the executable Wagner--Fischer
recurrence computes this distance, tying the finite super-condensed
neighborhood calculation to the source's stated metric.

## Falsifier

The route would fail if the displayed neighborhood enumeration were incorrect
under the minimum-alignment-cost definition. A failure of
`levenshtein_eq_dlev`, or a proof that the displayed three-element set has
cardinality at most the corresponding two-element set, would also invalidate
the refutation.

## Evidence

- Frozen identity:
  `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.levenshtein_eq_dlev`.
- Frozen super-condensed refutation:
  `D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultSuperCondensed`.
- The formal claim quantifies the alphabet, length, radius, unary letter, and
  comparison word, and retains the source's unrestricted radius.

## Triage

`theorem`; resolution `refuted`. The identity and super-condensed refutation
have `proof_shape: content`. The identity has
`admission_basis: escape-witness`; the published-question refutation has
`admission_basis: open-problem-resolution` under preregistration #8618.

## ASSUMED-UNVERIFIED

The literature review is bounded and does not establish exhaustive absence
of corrections, unpublished work, paywalled citing papers, or unindexed
resolutions. No worldwide novelty or publication-priority claim is made.
