---
slug: hardin-a235310-alphabet-comparison
bibkey: hardin2014a235310
doi: null
url: https://oeis.org/A235310
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T
---

# Hardin's A235310 alphabet comparison

## Problem

For every $n,k\ge 1$, prove $C(5,6;n,k) = C(6,8;n,k) = C(7,10;n,k)$, where $C(M,S;n,k)$ counts literal indexed $(n+1)\times(k+1)$ grids over $0,\ldots,M$ with absolute diagonal difference $S$ in every contiguous $2\times2$ block. The NAME is the first count and the three choices are $i=1,2,3$ in the COMMENT. [OEIS A235310, revision 7](https://raw.githubusercontent.com/oeis/oeisdata/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A235/A235310.seq) · [Library note](../Library/Automata/hardin2014a235310.md)

| Source clause | Lean counterpart |
| --- | --- |
| OFFSET `1,1` and a grid of size $(n+1)\times(k+1)$ | Hypotheses `1 ≤ n` and `1 ≤ k` and domain `Fin (n + 1) × Fin (k + 1)`. |
| Alphabet from zero to the chosen maximum | `Fin (M + 1)` contains precisely the entries $0,\ldots,M$. |
| Every contiguous block has the stated absolute difference | Each corner ranges over `Fin n × Fin k`. The maps `castSucc` and `succ` select the consecutive indices. `Int.natAbs` is applied after taking the difference of the two integer sums. |
| The three literal counts agree | `C` takes `Nat.card` of the subtype of legal functions. The endpoint `a235310` asserts both consecutive equalities. |

## Motivation

This Tier 1 empirical comparison tests whether increasing the alphabet and stress together preserves the rectangular count. The frozen A235289 count supplies the neighboring literal rectangular model. [Preregistration #34296](https://github.com/the-omega-institute/trureturing/issues/34296)

## Gap

The scoped search in #34296 found no resolution for this deficit. The nearby A235289 equality concerns deficit two. The surveyed binary window-sum and finite reconstruction results have different scopes.

## Route

At deficit 4, checkerboard complementation produces block sums $4$ and $4M-4$. Their gap exceeds $2M$, the maximum change across a shared edge, so the block sum is uniform. Whole-grid complementation exchanges the classes. Each cell belongs to a block, so every entry in the low class is at most 4. Alphabet restriction and embedding give inverse maps. Each of the three counts is twice the exact cardinality of the same sum-4 class over `Fin (4 + 1)`.

## Falsifier

Two unequal counts at any positive pair of indices among the stated three alphabet and stress pairs would refute the claim.

## Evidence

The scratch Lean declaration `D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235280A235310Alphabet.a235310` typechecks at the exact literal conclusion and depends on `propext`, `Classical.choice` and `Quot.sound`. The literature-attested empirical clause has a repository-derived proof.

## Triage

The public conclusion concerns all positive rectangles at the three explicit choices of $i$. The parameterized normalization proves both equalities in the displayed comparison. Other choices of $i$ and recurrence questions were outside the registered event. [Preregistration #34296](https://github.com/the-omega-institute/trureturing/issues/34296)

## ASSUMED-UNVERIFIED

Global priority remains unverified. The bounded literature screen in #34296 records the OpenAlex HTTP 429, unavailable publisher PDFs and incomplete citation coverage.
