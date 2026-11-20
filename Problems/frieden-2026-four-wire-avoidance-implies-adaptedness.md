---
slug: frieden-2026-four-wire-avoidance-implies-adaptedness
bibkey: frieden2026bigcactus
doi: 10.48550/arXiv.2610.24842
url: https://arxiv.org/html/2610.24842v1#S4.Thmtheorem10
triage: theorem
motivation_gids:
  - D5/S1/Words/Permutations/FriedenAdaptedWords.avoidance_implies_adapted
---

# Four-wire avoidance implies adaptedness

## Problem

Conjecture 4.10 of Frieden, Pylyavskyy and Rybnikov asks whether reduced
reversal words are $X$-avoiding exactly when adapted to a path orientation.
The open implication asks whether $X$-avoidance implies adaptedness.
Theorem 4.9 and Lemma 4.5 give the converse in the source.

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| A reduced word for the reversal on $n$ wires | `w : Word n` and `ReducedReversal w`, requiring length $n(n-1)/2$ and reversal after the chronological adjacent swaps from identity |
| Subnetwork induced by four selected wires | For each `S : Finset (Fin n)` of cardinality four, `restrict w S` keeps precisely swaps internal to $S$ and renumbers them by selected position |
| $X$-avoidance | `AvoidsX w`, requiring every such restriction to lie outside $\{123212,321232,212321,232123\}$ |
| Adapted to an orientation of $A_{n-1}$ | `Adapted w`, existence of an initial edge orientation for which every letter is a source at its step, followed by the incident-edge flip |

The theorem quantifies over every natural $n$. Below two wires the Lean
generator type is empty.

## Motivation

The implication connects an obstruction on four selected wires with
the existence of an orientation that permits the entire chronological word.
The original conjecture and its preregistration are linked below.
[Conjecture 4.10](https://arxiv.org/html/2610.24842v1#S4.Thmtheorem10) · [#32071](https://github.com/the-omega-institute/trureturing/issues/32071)

## Gap

The necessity established by the source leaves sufficiency of the four
literal restrictions. The sufficiency proof must prescribe every retained
crossing, including crossings outside the interval between repeated letters.

## Route

A nonalternating projection gives two equal generators with neither edge
endpoint between them. When the repeated generator is the left endpoint,
the position to its right stays fixed and the block farther right preserves
its labels. The repeated swaps and one crossing in the left block force
`212` on three selected wires. A fourth wire from the right block can
participate before this interval only by moving right and after it only
by moving left. Its initial rank gives the two complete sequences around
`212`. Reflection gives the other endpoint case.

## Falsifier

An avoiding reduced reversal word with a nonalternating adjacent-generator
projection would contradict the implication. A quartet whose computed
chronological restriction differed from the rank prescription would
invalidate the obstruction argument.

## Evidence

The proof uses pair uniqueness from the exact reversal length. The
restriction counts selected positions before each retained swap. Comparing
ranks before and after each retained crossing gives the complete restricted
word. The edge orientation is chosen from the first occurrence on each edge.

## Triage

The avoidance-to-adaptedness implication is proved by
`Frieden.avoidance_implies_adapted`. The cited paper establishes the
adaptedness-to-avoidance implication. Literature coverage is bounded by
the primary source and the searches listed in the preregistration.
