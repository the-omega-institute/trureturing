---
slug: oeis-a391620-first-sums-partition-characterization
bibkey: wiseman2025a391620
doi: null
url: https://oeis.org/A391620
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/FirstSumsPartitionCharacterization
---

# First sums of decreasing partitions

## Problem

OEIS A391620 (Gus Wiseman, Dec 30 2025) states:

NAME "Number of integer partitions of n that are not the first sums of any composition with all parts > 1."

COMMENT "Conjecture: These are integer partitions of n whose least part is < 4."

The NAME line is copied verbatim from `Library/Words/wiseman2025a391620.md`.
The reading used by Lean writes a partition q as a weakly decreasing,
nonempty list of positive parts. It is the first sums of a composition
x = (x_1, ..., x_{r+1}), with every x_j >= 2, exactly when
q_i = x_i + x_{i+1} for each i. Equality preserves this order; it is not
equality after arbitrarily permuting the adjacent sums. The conjecture is
equivalent to `(not first sums) iff min q < 4`. For a nonempty partition,
the latter condition is equivalent to the existence of a part below four.

## Motivation

This is a first-tier recent OEIS conjecture. The KPI is open problems
resolved, and the target is the universal characterization and its partition
counting corollary, with no finite search bound.

## Gap

The supplied search report found no proof in the searched scope: the search
seat read the OEIS entry and revision history on 2026-09-08 and searched
arXiv, MathOverflow and GitHub by identifier. This Stage-B seat had no network
access and did not repeat that search. This report does not establish an
exhaustive literature search or first-publication priority.

## Route

Necessity: if q = firstSums x and every part of x is at least two, each
adjacent sum is at least four (`min_ge_four_of_isFirstSums`).

Sufficiency: the private lemma `reconstruct` builds a realization backward
from the suffix, maintaining `2 <= x_i <= q_i - 2` at its leading endpoint.
For a singleton [a], use [a-2,2]. If the suffix begins at b and its first
reconstructed entry is u, prepend a-u. Weak decrease gives b <= a, so
`2 <= u <= b-2` implies `2 <= a-u <= a-2` and `(a-u)+u = a`.
This proves `isFirstSums_of_sorted_min_ge_four`; combining the directions
gives `wiseman_conjecture`.

The counting corollary `card_not_firstSums_eq` restates the OEIS count as
the number of partitions with a part below four, hence least part below
four for nonempty partitions. It also covers n = 0: the empty target is
realized by [2], and both filters count zero. There is no D5 import; the
sole import is `Mathlib.Combinatorics.Enumerative.Partition.Basic`.

## Falsifier

A counterexample index n would admit a weakly decreasing positive partition
q of n that has every part at least four but no such realization, or a
realizable q with a part below four. A disagreement between the two counts
at any n would also contradict the counting corollary. The orchestrator's
exact finite check is supporting evidence only, not the universal proof;
this seat did not rerun it or independently verify its bounds.

## Evidence

- Lean module: `D5/S1/Words/Compositions/FirstSumsPartitionCharacterization.lean`.
- Main theorem: `wiseman_conjecture`.
- Companions: `min_ge_four_of_isFirstSums`,
  `isFirstSums_of_sorted_min_ge_four`, `card_not_firstSums_eq`, `firstSums_length`.
- Definitions: `firstSums`, `IsFirstSums`.
- Axioms: std3 (`propext`, `Classical.choice`, `Quot.sound`), as recorded for
  all five public theorems in the implementation seat's successful compile.
- The list theorem permits zero parts; positivity comes from
  `Nat.Partition n` in the counting corollary. The nonempty list theorem and
  the empty-partition extension have separate hypotheses and scope.

## Triage

`theorem`. The formal proof closes the universal assertion under the
weakly decreasing ordered-part reading recorded above.

## ASSUMED-UNVERIFIED

The OEIS quotes, author and date were supplied by the orchestrator. The
Library note lacked the verbatim NAME line at Stage-B intake; Stage-B added
the exact supplied sentence before copying it here. OEIS revision history
was read by the search seat, not by this seat. The supplied literature scope
was the OEIS entry/history and identifier searches on arXiv, MathOverflow
and GitHub on 2026-09-08; this seat had no network access. No exhaustive
literature or third-party Lean ecosystem search, nor first-publication
priority, is claimed. Source-to-Lean identification and the external search
report are not kernel-checked facts. This seat did not rerun the axiom report
or the orchestrator's finite check.
