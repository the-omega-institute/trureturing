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

OEIS A261041 NAME counts “partitions of subsets of {1,...,n}, where consecutive integers are required to be in different parts.” In COMMENTS, Gus Wiseman wrote on 25 November 2019, “Conjecture: Also the number of set partitions of {1, ..., n + 1} where, if x and x + 2 belong to the same block, then so does x + 1.” The electronic entry has revision #44 and offset 0,2. [Source](https://oeis.org/A261041/internal)

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| For every integer n ≥ 0 | The explicit binder `(n : ℕ)` in `result`. |
| Partitions of all subsets of the first n positive integers | `PartialPartition n` consists of an arbitrary `Set (Fin n)` and a `Setoid` on that subtype. Index i represents the integer i+1. |
| Consecutive integers in different blocks | `NoConsecutive` forbids `SameBlock` for every adjacent pair in the ambient interval. The relation requires both points to belong to the carrier. |
| Full partitions of the first n+1 positive integers | `Right n` restricts `Setoid (Fin (n+1))` by `TripleCondition`. |
| Each consecutive triple | For every i with i+2 < n+1, `TripleCondition` requires that i and i+2 lying in the same block imply i and i+1 lie in the same block. |
| Equality of the counts | `result n : Nat.card (Left n) = Nat.card (Right n)`. |
| Registered refinement by block count | The value of `wisemanBijection n` is an equivalence of those literal partition types. Its proof component says that the target quotient has one more class for every input. |

## Motivation

This named external conjecture was preregistered as Tier 1 under the open-problem-resolution basis. The source and scoped literature screen are recorded in the preregistration. The public settlement reports the bijection, the block-count shift and the independently replayed proof. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/34937) · [Registered quantifiers](https://github.com/the-omega-institute/trureturing/issues/34937#issuecomment-7225772584) · [Public settlement](https://github.com/the-omega-institute/trureturing/issues/34937#issuecomment-7226553589)

## Gap

The source generating function counts the partial partitions. The missing comparison was with full partitions subject to the triple implication. A map on representatives needs an inverse on literal partitions and a proof that renaming representatives has no effect on the resulting equivalence relation.

## Route

Adjoin a first position whose block contains all omitted positions. On the resulting full partition of the padded interval, label each block by its least position. Start at the identity permutation with output zero. At each step emit the image of the input label under the current permutation, then compose the permutation on the right with the swap of zero and that input label. The inverse recovers the input with the inverse current permutation and uses the same update. The scan commutes with relabeling that fixes zero. Its induced action on setoids is an equivalence.

The decisive identity pairs an output triple with equal endpoints and a different middle with two successive equal nonzero input labels. The scan preserves the used labels. Removing the block of the initial position inverts padding, and padding adds one block. Together these facts yield the pointwise block-count shift.

## Falsifier

A qualifying partial partition whose image violated the triple condition, two distinct qualifying partial partitions with the same image, or a qualifying full partition with no inverse would defeat the proposed bijection. A different target quotient cardinality from the source cardinality plus one would defeat the refinement.

## Evidence

The Lean owner is `D5/S3/Combinatorics/Partitions/WisemanA261041.lean`. Its theorem is `D5/S3/Combinatorics/Partitions/WisemanA261041.result`. The original proof was independently rebuilt and kernel-replayed byte-for-byte on Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The public settlement records its axiom closure as `propext`, `Classical.choice` and `Quot.sound`. [Public settlement](https://github.com/the-omega-institute/trureturing/issues/34937#issuecomment-7226553589)

The native source-bound registration for the counting theorem has a `declared_validated` binding. Its readout is the left-hand count, with the full quantifier and right-hand count retained in the law. The residual is open.

## Triage

### What the settlement shows

- **Proved.** The cardinalities agree for all n. The equivalence refines the identity by the number of blocks through its pointwise shift. The two statements are recorded at `D5/S3/Combinatorics/Partitions/WisemanA261041.result` and `D5/S3/Combinatorics/Partitions/WisemanA261041.wisemanBijection`.
- **Proved.** The zero boundary matches the empty partial partition with the unique full partition of a singleton. Both counts are one.
- **Open.** Further avoidance conditions that admit an analogous padded scan are outside the stated result.
- The checked source material records no other published result depending on the conjecture. The generating function for the original class therefore also enumerates the full partitions of the stated type, by the proved equality. [Source entry](https://oeis.org/A261041/internal) · [Generating function](https://mathoverflow.net/q/478446)

## ASSUMED-UNVERIFIED

The literature screen covers the OEIS record, the linked generating-function answer, the cited consecutive-subword and succession comparisons, an accessible monograph excerpt and exact-identifier searches. The remainder of the monograph and completeness of the search remain unverified. [Preregistration](https://github.com/the-omega-institute/trureturing/issues/34937)
