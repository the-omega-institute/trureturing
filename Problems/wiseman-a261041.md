---
slug: wiseman-a261041
bibkey: wiseman2019a261041
doi: null
url: https://oeis.org/A261041/internal
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/WisemanA261041.result
---

## Problem

The NAME field of OEIS A261041 counts “partitions of subsets of {1,...,n}, where consecutive integers are required to be in different parts.” Gus Wiseman's comment of 25 November 2019 adds “Conjecture: Also the number of set partitions of {1, ..., n + 1} where, if x and x + 2 belong to the same block, then so does x + 1.” The offset is 0,2 and the conjecture includes the singleton full partition at $n=0$. [OEIS A261041](https://oeis.org/A261041/internal)

| Source clause | Lean counterpart |
| --- | --- |
| Every natural number $n$, including $0$ | The explicit binder `(n : ℕ)` in `result`. |
| Partitions of every subset of $\{1,\ldots,n\}$ | `PartialPartition n` consists of a carrier `Set (Fin n)` and a setoid on that subtype. Index $i$ represents $i+1$. |
| Consecutive integers in different blocks | `NoConsecutive` forbids `SameBlock` at every adjacent pair in the ambient interval. The relation requires both points to belong to the carrier. |
| Full partitions of $\{1,\ldots,n+1\}$ | `Right n` restricts setoids on `Fin (n + 1)` by `TripleCondition`. |
| Every consecutive triple | For each $i$ with $i+2<n+1$, `TripleCondition` says that equal blocks at $i$ and $i+2$ imply equal blocks at $i$ and $i+1$. |
| Equality of the two counts | `result n : Nat.card (Left n) = Nat.card (Right n)`. |

## Motivation

The sequence pairs a restriction on adjacent positions in partial partitions with a restriction on triples in full partitions. The conjecture was registered as a Tier 1 external open problem. The registered block-count refinement concerns the same construction. A separate public proof report for the conjecture is available in the issue discussion. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/34937) · [Registered quantifiers](https://github.com/the-omega-institute/trureturing/issues/34937#issuecomment-7225772584) · [Public proof report](https://github.com/the-omega-institute/trureturing/issues/34937#issuecomment-7226553589)

## Gap

The linked inclusion–exclusion answer gives a generating function for the partial partitions. The comparison needs a bijection with the stated full partitions. A scan on labels must be invertible and independent of the chosen labels on the blocks. The cited papers on consecutive subwords and successions concern different restrictions. [Generating function](https://mathoverflow.net/q/478446) · [Mansour–Shattuck–Yan](https://doi.org/10.37236/291) · [Munagi](https://doi.org/10.1155/IJMMS.2005.451)

## Route

Adjoin an initial position whose block also contains the omitted positions. Label each resulting block by its least position. Start with output zero and the identity permutation. For each input label, emit its image under the current permutation and compose the permutation on the right with its swap with zero. The inverse applies the inverse permutation to the current output and makes the same update. The scan commutes with relabelings fixing zero, so it induces an equivalence of literal full partitions. Removing the block containing the initial position inverts padding.

An output triple has equal endpoints and a different middle exactly when its two corresponding successive input labels are equal and nonzero. The equivalence therefore restricts to `Left n ≃ Right n`. The equality of counts follows by applying `Nat.card_congr`.

For the block-count interpretation, the permutation at each step fixes labels absent from the input prefix. Thus a first occurrence is emitted unchanged and a repeated label is emitted within the already used labels. Starting from the singleton label set containing zero, the set of used labels agrees on both sides at every step. Padding adds one block, so the construction explains the one-block shift. The local Lean declarations certify the equivalence and the total counts.

## Falsifier

An allowed partial partition sent to a forbidden full partition, two distinct allowed inputs with the same image, or an allowed full partition without an inverse would defeat the proposed bijection. A prefix where the used label sets differed would defeat the argument for the block-count refinement.

## Evidence

`D5.S3.Combinatorics.Partitions.WisemanA261041.wisemanBijection` is the literal equivalence for each $n$. The frozen declaration `D5.S3.Combinatorics.Partitions.WisemanA261041.result` gives the source equality on the pinned Mathlib backend. Both have axiom closure `propext`, `Classical.choice` and `Quot.sound`.

The Reg mirror supplies a `declared_validated` source-equivalence registration for `result`. The readout is the left-hand count and the law retains the natural-number quantifier and the right-hand count. The registration binds the source theorem to the law, supplies the actual readout and a rejected constant-zero readout, and witnesses actual dependence at states $0$ and $1$. The continuation is open.

## Triage

- **Proved.** The two cardinalities agree for every natural number by `result`, with the literal equivalence given by `wisemanBijection`.
- **Proved.** The zero boundary has cardinality one on both sides. The Reg mirror's `right_zero` gives the singleton count on the right, and `result 0` transports it to the left.
- **Proved by the prefix argument.** The scan preserves the set of used labels and padding adds one block. This gives an explanatory pointwise refinement. The frozen theorem states the equality of total counts.
- **Proved.** The generating function for the partial class also enumerates the stated full class by `result`. The checked sources identify no further dependent published result. [Generating function](https://mathoverflow.net/q/478446)
- **Open.** Which other local avoidance conditions admit a corresponding reversible scan.

## ASSUMED-UNVERIFIED

The literature check covered the OEIS record, the generating-function answer, the two cited pattern papers, an accessible monograph excerpt and exact-identifier searches. The rest of the monograph and completeness beyond those sources remain unverified. The separate public proof report documents a proof for this conjecture. [Literature scope](https://github.com/the-omega-institute/trureturing/issues/34937) · [Public proof report](https://github.com/the-omega-institute/trureturing/issues/34937#issuecomment-7226553589)
