---
slug: oeis-a392698-trimmed-alternating-partitions
bibkey: oeis2026a392698
doi: null
url: https://oeis.org/A392698
triage: theorem
motivation_gids:
  - D5/S1/Words/Compositions/TrimmedAlternatingPartitions
---

# Trimmed Alternating Sums of Ordinary Partitions

## Problem

For an ordinary partition q of n, list the positive parts in weakly
decreasing order. Set s_0=0 and s_j=q_j-s_(j-1) in the integers. Count
partitions for which s_1,...,s_k are pairwise distinct, excluding s_0.
The corrected conjecture asserts that this count is the number of
partitions of n+1 into distinct positive parts, for every n including zero.
The unshifted A000009(n) sentence on A392698 is incorrect; the source note
records the correction and the equivalent conjectural A392703 comment.

## Motivation

This is a first-tier recent OEIS conjecture. The previous worker audited
all 42 source xrefs and found the exact shifted statement qualified by
"we appear to have" on A392703. That is a conjectural restatement, not a
published proof. The corrected implementation brief explicitly replaces
the previous rule that stopped upon finding any equivalent statement.

## Gap

The pinned Mathlib provides Nat.Partition.distincts but the inspected
statements do not give this integer alternating-sum characterization or
shifted bijection. A fresh Mathlib-only probe of the exact list equivalence
left both directions unsolved. This is a search receipt, not a proof of
absence of every possible library composition. No published proof was
identified in the recorded source audit; exhaustive absence is unclaimed.

## Route

The structural theorem proves that trimmed sums are distinct exactly when
q.tail is strictly decreasing. Its integer range invariant uses two steps
of the recurrence; repeated neighboring tail parts force equal sums two
positions apart. The first two parts may be equal.

Increase the largest part by one, sending [] to [1]. The image is strictly
decreasing and has weight n+1. Conversely, a strict positive partition of
n+1 is nonempty; send [1] to [] and otherwise decrease its maximum by one.
Positivity, order, weights and both inverse laws are proved. The equivalence
of the filtered Mathlib partition types yields the exact cardinal equality.

## Falsifier

A positive decreasing list violating the strict-tail equivalence, or a
weight at which the two finite-set cardinalities differ, would refute the
respective statement. The test domains are unbounded. Natural subtraction,
including s_0 in the distinctness test, requiring the entire input to be
strict, or omitting the n=0 case would change the problem.

## Evidence

The new module is D5/S1/Words/Compositions/TrimmedAlternatingPartitions.lean.
Its public theorems are trimmedSums_nodup_iff_strict_tail and
card_trimmedSums_eq_distincts. The warm-tree file check exited 0 and reported
only propext, Classical.choice and Quot.sound for both. make lean LAKE_JOBS=3
exited 0 with 12,763 jobs. The initial cache receipt, bind-only failure,
proof-shape analysis and remaining delivery checks are in the existing
Library note and the worker-owned runner report.

The supplied mathematical route was derived by the previous worker and
independently checked finitely by the caller. The previous worker's
n=0,...,30 enumeration and the caller's n=0,...,20 enumeration are attributed
input evidence; this worker does not claim to have rerun those enumerators.
They did not constitute the kernel proof now provided by the new module.

Worker-owned Boundaries.lean imports the built module and exits 0. Its
outputs are [2,0,1], [3,-1,3,-2], [], [2], and [1,0] for the specified
inputs. Kernel checks certify the first example's Nodup and strict tail,
the second example's failure of both predicates, and that [2,2,1] is not
strict as a whole. They also certify that [1,1] qualifies when trimmed and
fails if the initial zero is prepended. Separate checks prove that the
qualified weight-zero filter has cardinality 1 and distincts(1) has
cardinality 1. These boundary checks are diagnostics, not a finite
replacement for the general theorem.

## Triage

`theorem`: the exact unbounded structural and cardinality statements are
implemented. The Scribe resolution claim refers to the corrected statement
in this dossier. The unshifted source sentence is not being certified.
Kernel truth, documentary source fidelity, literature priority and PR
merge status are distinct claims; final delivery receipts identify them.

## ASSUMED-UNVERIFIED

No exhaustive literature search, first-publication priority, or implication
to any larger conjecture is claimed. Source fidelity is documentary; the
kernel checks the explicitly defined recurrence, hypotheses and finite
sets. Skill context is lean4 within the caller's consensus-rnd:sshx
implementation task. One Codex worker implements and self-checks; no
independent review or multi-model consensus is claimed by this dossier.
The caller's prior enumeration is reported, not relabeled as worker data.
