---
slug: frieden-2026-adapted-reversal-words
bibkey: frieden2026bigcactus
doi: 10.48550/arXiv.2610.24842
url: https://arxiv.org/html/2610.24842v1#S4.Thmtheorem10
triage: theorem
motivation_gids:
  - D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410
  - D5/S1/Words/Permutations/FriedenAdaptedWords.avoidance_implies_adapted
---

# Four-wire avoidance and adapted reduced reversal words

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

The closed Lean proposition `D5.S1.Words.Permutations.Frieden.claim : Prop` is
`∀ (n : Nat) (w : Word n), ReducedReversal w → (AvoidsX w ↔ Adapted w)`.
The exact result `D5.S1.Words.Permutations.Frieden.conjecture410` has type `claim`.
Both directions quantify over every natural $n$. Below two wires the Lean
generator type is empty. The distinct forward theorem
`D5.S1.Words.Permutations.Frieden.avoidance_implies_adapted` proves
`∀ (n : Nat) (w : Word n), ReducedReversal w → AvoidsX w → Adapted w`.

## Motivation

The implication connects an obstruction on four selected wires with
the existence of an orientation that permits the entire chronological word.
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

For the converse, moving a wire into an interior position reverses the
arrow on the edge between its two possible next generators. The next
move cannot take that wire back. A wire turning twice would cross the
whole network between its turns, requiring more than $n-1$ moves.
The direction list of each restricted wire is a subsequence of the
full direction list. Each word in $X$ exhibits a selected wire that
turns twice.

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

The two source-equivalence registrations use the actual Boolean avoidance
readout on words of every rank. The reduced word `123212` witnesses failure
of the law under the constant-true intervention. The local native report
validates the following bindings. Both continuations are recorded as unknown.

| Scribe Describe ID | Lean output GID | Registration |
| --- | --- | --- |
| `frieden-avoidance-implies-adapted` | `D5/S1/Words/Permutations/FriedenAdaptedWords.avoidance_implies_adapted` | `avoidance_implies_adaptedRegistration` in the AdaptedWords Reg mirror |
| `frieden-conjecture-410` | `D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410` | `conjecture410Registration` in the same mirror, with the readout selected in the body of `claim` |

Section 3.9 registration remains open for these nine public theorems in
`FriedenSortingNetwork`: `left_ne_right`, `restrict_cons`, `rank_step_stay`,
`rank_step_move_right`, `rank_right_before`, `rank_step_move_left`,
`quartet_left`, `wire_directions_bound`, and `rank_other`. Each needs a
typed owner registration reproducing its original observations, with an
enrolled readout, whole-statement reconstruction, actual law, variation,
sensitivity, and observational dependence.
[Statement-specific registration gaps](https://github.com/the-omega-institute/trureturing/issues/32071#issuecomment-7031371797)

## Triage

- **Proved in Lean.** The four-wire avoidance equivalence in all natural ranks
  is `D5/S1/Words/Permutations/FriedenAdaptedWords.conjecture410`. The
  avoidance-to-adaptedness implication is separately available at
  `D5/S1/Words/Permutations/FriedenAdaptedWords.avoidance_implies_adapted`.
- **Open in Lean.** For a reduced reversal word with paper indices
  $i_1,\ldots,i_N$ and $N=\binom{n}{2}$, the source uses Meng's formula to
  identify avoidance with $\sum_{r=1}^N(i_r-1)(n-i_r-1)=2\binom{n}{4}$.
  The counting formula and its bridge to avoidance remain open in Lean,
  as does an enumeration formula for the common class.
- **Literature scope.** The bounded source and literature search is recorded
  in [#32071](https://github.com/the-omega-institute/trureturing/issues/32071).
  The full forward bibliography is unverified.

### What the settlement shows

- **Proved in Lean.** Exact length and reversal force each pair to cross once.
  In the forward implication, a repeated endpoint letter in a failed
  adjacent-generator projection fixes a four-wire obstruction, with all
  retained prefix and suffix crossings determined by the initial rank of
  the fourth wire. Reflection supplies the other endpoint case. Alternation
  on every edge allows an initial orientation chosen from the first endpoint
  visited. In the converse, a source flip prevents an interior turn, pair
  uniqueness bounds the number of moves of a wire, and a four-wire
  restriction preserves its moves as a subsequence. These arguments prove
  the equivalence at every rank under `ReducedReversal`.
  `D5/S1/Words/Permutations/FriedenSortingNetwork.quartet_left` supplies the
  left-endpoint obstruction used by the two AdaptedWords outputs.
- **Consequence of the proved equivalence.** The two sets of reduced words
  are equal, so their cardinalities agree. The enumeration problem in §9.4
  therefore becomes enumeration of adapted reduced words. The paper's
  further identification with linear extensions of Auslander–Reiten quivers
  is a literature statement.
  [§9.4](https://arxiv.org/html/2610.24842v1#S9.SS4)
- **Open here.** The argument uses reducedness and reversal to control every
  pair of labels. A characterization with either hypothesis relaxed lies
  outside the proved scope.

## ASSUMED-UNVERIFIED

The numerical reformulation via Meng's formula and the identification with
linear extensions of Auslander–Reiten quivers are cited literature results
outside the two Lean outputs. The full forward bibliography remains unverified.
