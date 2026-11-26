---
slug: hardin-a235289-alphabet-comparison
bibkey: hardin2014a235289
doi: null
url: https://oeis.org/A235289
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.T
---

# Hardin's comparison of four constant-stress alphabets

## Problem

Let $T(n,k)$ count literal $(n+1)\times(k+1)$ arrays with entries
$0,1,2,3$ and absolute diagonal difference four in every contiguous
$2\times2$ block. The OFFSET is `1,1`. In the COMMENT, Hardin writes

> Empirical: T(n,k) is the number of (n+1) X (k+1) 0..2+i arrays with every 2 X 2 subblock having its diagonal sum differing from its antidiagonal sum by 2+2*i (constant-stress 1 X 1 tilings) for i=1..4(..?).

For every $n,k\ge 1$ and each $i\in\{1,2,3,4\}$, the conjectured
equality compares that literal count with $T(n,k)$. The explicit alphabet
maximum and stress pairs are $(3,4)$, $(4,6)$, $(5,8)$, and $(6,10)$.
[Library note](../Library/Automata/hardin2014a235289.md) ·
[OEIS A235289, revision 7, June 18, 2022](https://raw.githubusercontent.com/oeis/oeisdata/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A235/A235289.seq) ·
[Preregistration #34261](https://github.com/the-omega-institute/trureturing/issues/34261)

| Source clause | Lean counterpart |
| --- | --- |
| Positive rectangular dimensions | `n k : ℕ` with `1 ≤ n` and `1 ≤ k`, and axes `Fin (n + 1)` and `Fin (k + 1)`. |
| Four comparisons, alphabet 0 through 2+i | The hypothesis is `i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4`. An entry in `Fin (i + 3)` takes each of the stated values. |
| Every contiguous block, absolute diagonal difference 2+2i | The upper left corner ranges over `Fin n` and `Fin k`. The embeddings `castSucc` and `succ` pick each pair of consecutive indices. Entry values are cast to integers before subtraction and `Int.natAbs` is compared with `2 + 2 * i`. |
| Number of literal indexed arrays equals the original count | `HardinA235289Alphabet.literalCount n k i` is the `Nat.card` of the subtype of legal functions, cast to `ℤ`. The theorem `HardinA235289Alphabet.result` equates this count with `HardinA235289Recurrence.T n k`. |

## Motivation

The comparison asks whether growing the alphabet and raising the stress
in tandem preserves the count. The Tier 1 empirical conjecture has
admission basis `open-problem-resolution`.

## Gap

The empirical assertion in the pinned revision concerns all positive
rectangles. The scoped literature and repository screen recorded in #34261
located related finite enumeration and binary window problems. Establishing
the comparison requires the rectangular argument at the stated alphabet
maxima.

## Route

At alphabet maximum $M=i+2$, complement the entries on one checkerboard
color in $M$. The allowed block sums become $2$ and $4M-2$. The two sums
differ by more than $2M$ for $M\ge 3$. Blocks sharing an edge can differ
by at most $2M$, so the block sums throughout the rectangle agree.

Complementing all entries exchanges the two uniform classes. When the
block sum is two, every entry belongs to $\{0,1,2\}$, because the entries
are nonnegative and every cell belongs to some contiguous $2\times2$
block. Thus value-preserving restriction and embedding give inverse maps
between the low class over the current alphabet and the low class over
three symbols. The canonical four-symbol identity
`HardinA235289Recurrence.original_eq_twice_low` identifies $T(n,k)$
with twice the same low count using the three-to-four-symbol embedding.

## Falsifier

An exact literal count at any positive rectangle for one of the four
listed parameter pairs that differs from $T(n,k)$ would refute the claim.

## Evidence

`HardinA235289Alphabet.result` and its dependent-family registration
`Reg.D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Alphabet.audit`
have axiom closure `propext`, `Classical.choice`, and `Quot.sound`. The
registered law equates `literalCount n k i` with the readout at `n, k`
for every positive pair and each of Hardin's four values of `i`. The
actual readout is `T n k`. Increasing just its value at `(1, 1)`
breaks the law at `n = k = i = 1`. Actual dependence on the column
index is witnessed by `T 1 1 ≠ T 1 2`.

## Triage

The equality concerns literal counts over indexed rectangles. The
published range for the comparison is the four explicit values of $i$.
The positive dimensions ensure that every cell participates in the
block condition.

## ASSUMED-UNVERIFIED

Global priority is unverified. The literature screen in #34261 records
an OpenAlex HTTP 429 and an HTTP 403 for the historical revision view.
