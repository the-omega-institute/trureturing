---
slug: chauve-zhang-condensed-neighborhood-unary-minimality
bibkey: chauve2025neighborhoods
doi: 10.48550/arXiv.2505.13796
url: https://arxiv.org/abs/2505.13796v2
triage: theorem
motivation_gids:
  - D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed
---

# Condensed neighborhoods of unary words need not be smallest

## Problem

Chauve and Zhang, *On the size of the neighborhoods of a word*,
arXiv:2505.13796v2, Section 6 (Conclusion) on printed page 7:

> It is thus natural to ask if a similar property holds for condensed and super
> condensed neighborhoods, namely that unary words have the smallest condensed
> or super condensed neighborhoods.

with, on printed page 2, `N(w, d) = {x ∈ Σ* | d_lev(x, w) ≤ d}` (2.1) and

> The condensed d-neighborhood of w, written as CN(w, d), consists of the
> words of N(w, d) which do not have a prefix in N(w, d), that is,
> CN(w, d) = N(w, d) \ N(w, d)Σ⁺. (2.2)

and "A word w is unary if it consists of multiple occurrences of a single
character from Σ, i.e., w = σ^{|w|} for some σ ∈ Σ."

The first assertion of that sentence, with its quantifiers written out: for
every finite alphabet Σ, all `n, d`, every letter σ ∈ Σ and every word `w` of
length `n`, `|CN(σⁿ, d)| ≤ |CN(w, d)|`.

## Motivation

The question seeks lower bounds for condensed-neighborhood size by using
unary words as minimizers. A binary word of length three at edit radius two
tests the universal statement inside the range of the paper's unary formula.

## Gap

Issue #8618 records the exact source sentence, full quantifiers, and a
bounded literature check. Version 2 retains the question. The checked arXiv
queries returned only the source paper, and the checked Semantic Scholar
citation surface contained no settlement. This is a bounded result, not an
exhaustive worldwide priority claim.

## Route

Use the binary alphabet with unary word `000`, comparison word `001`, and
radius two. The formal Wagner--Fischer recurrence gives
`CN(000,2) = {0,10,110}` and `CN(001,2) = {0,1}`. A length estimate proved
from the recurrence places every neighborhood member in a finite list
universe, so these set cardinalities reduce to three and two. The required
inequality would therefore be `3 <= 2`, a contradiction.

## Falsifier

An error in either displayed finite condensed neighborhood, in the
length bound used to obtain a finite carrier, or in the translation of
equation (2.2) to proper-prefix minimality would invalidate this refutation.

## Evidence

The frozen theorem
`D5/S1/Words/ChauveZhangUnaryNeighborhoodRefutation.resultCondensed :
Not claimCondensed` has declaration identity
`sha256:47bff2142a91113a3669118ba9aeb1aa20fa62975c39cfc1e953b26fcbaacbf4`.
It belongs to Freeze event
`sha256:8b6c00bc5d3e6c8b52aa1ac8e14df78ab5d93479107cc07611b18c2d2f5704e4`.
Its axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`; the outcome is `refuted`. The theorem has `proof_shape: content`
with escape witness `length_le_add_levenshtein`: the local recurrence
induction is used on the live path that identifies the infinite set with a
finite carrier before its cardinality is reduced. The admission basis is
`open-problem-resolution` for preregistered issue #8618.

## ASSUMED-UNVERIFIED

The formal recurrence is not accompanied by an edit-script datatype and a
proof that it equals the minimum edit-script cost. Source-to-Lean fidelity
and literature completeness are not kernel-checked; the bounded searches
listed in issue #8618 do not exclude every prior or unpublished resolution.
