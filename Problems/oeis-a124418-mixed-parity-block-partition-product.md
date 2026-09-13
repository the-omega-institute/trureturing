---
slug: oeis-a124418-mixed-parity-block-partition-product
bibkey: hanna2006a124418
doi: null
url: https://oeis.org/A124418
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct
---

# Hanna's mixed-parity block partition product in A124418

## Problem

OEIS A124418, `%N` (verbatim):

> Triangle read by rows: T(n,k) is the number of partitions of the set {1,2,...,n} having exactly k blocks that contain both odd and even entries (0<=k<=floor(n/2)).

`%C` (verbatim):

> Row n has 1+floor(n/2) terms. Row sums are the Bell numbers (A000110). T(n,0)=A124419(n).

`%F` (verbatim; Paul D. Hanna, Nov 08 2006):

> Conjecture: T(n,k) = k!*A049020([n/2],k)*A049020([(n+1)/2],k) where A049020(n,k)=Sum_{i=0..n} S2(n,i)*C(i,k) and S2(n,k)=(1/k!)*Sum_{j=0..k} (-1)^(k-j)*C(k,j)*j^n (the Stirling numbers of 2nd kind).

The Lean definition `stirling2 r i` counts partitions of an `r`-element set
into `i` blocks, which is the object the source names as the Stirling numbers
of the second kind. The alternating-sum closed form for `S2` printed in the
FORMULA line is a standard identity for this object and is not formalized here.

## Motivation

This is a first-tier OEIS conjecture entered in 2006 and still presented as a
conjecture in the checked 2026 revision. The target is the complete product
formula over its stated range `0 <= k <= floor(n/2)` for every natural `n`.

## Gap

On 2026-09-13, the search and probe seats read all 26 OEIS revisions and the
linked entries A124526, A362495, and A049020, and searched exact identifiers
in zbMATH Open, Crossref, MathOverflow, and GitHub repository and commit
surfaces. No proof, refutation, or counterexample was found in the checked
surfaces. arXiv, OpenAlex, and GitHub code search returned 429 or 401 responses
and were not verified. This bounded search does not establish exhaustive
literature coverage or first-publication priority.

## Route

Split the carrier into its odd and even entries. The literal definition
`Tfin` counts partitions of `{1,...,n}` with exactly `k` blocks containing
both parities, and `T_eq_Tfin` identifies it with the parity-split model `T`.
The explicit equivalence
`mixedRestrictionEquiv : MixedParityPartition n k ≃ RestrictionPairingData n k`
restricts a partition to the odd and even summands, marks the `k` blocks on
each side that came from mixed blocks, and pairs their two halves. Gluing is
the two-sided inverse. Applying `Fintype.card_congr` gives
`T(n,k) = markedPartitions(ceil(n/2),k) * markedPartitions(floor(n/2),k) * k!`.
Finally, `markedPartitions_eq_A049020` decomposes by the total number of blocks
and contributes `Nat.choose` on each fiber, replacing each marked-partition
count by the corresponding A049020 value.

## Falsifier

A natural pair `(n,k)` with `k <= floor(n/2)` for which the literal count
`Tfin n k` differs from
`k! * A049020 (floor(n/2)) k * A049020 (ceil(n/2)) k` would contradict the
assertion. A failure of `T_eq_Tfin` would instead falsify the identification
of the parity-split model with the source's set-partition object.

## Evidence

- Lean module: `D5/S1/Recurrence/Partitions/MixedParityBlockPartitionProduct.lean`.
- Main theorem: `hanna_a124418`.
- Public bridge theorem: `T_eq_Tfin`.
- Public counting theorem: `markedPartitions_eq_A049020`.
- Public source-object definitions: `IsMixedBlockFin` and `Tfin`.
- Public restriction/gluing equivalence: `mixedRestrictionEquiv`.
- All three public theorems have exactly the std3 axioms: `propext`,
  `Classical.choice`, and `Quot.sound`.
- The orchestrator exhaustively enumerated set partitions for `0 <= n <= 9`
  and found zero mismatches. The probe separately checked both inverse laws of
  the restriction/gluing construction.
- The search seat reported that the OEIS b-file agrees through `n <= 200`;
  that comparison was not recomputed by the orchestrator and remains
  `ASSUMED-UNVERIFIED`.

## Triage

`theorem`. The formal proof establishes the full product identity on the
source's range. The addressable bridge `T_eq_Tfin` connects the theorem's
parity-split carrier `T` to the literal `%N` object `Tfin`.

## ASSUMED-UNVERIFIED

The OEIS quotation, revision count, attribution, search results, exhaustive
enumeration through `n <= 9`, and probe inverse-law check were supplied by the
orchestrator and preregistration issue #7408; this implementation seat did not
repeat them. The search seat's b-file comparison through `n <= 200` was not
recomputed by the orchestrator. No exhaustive literature or priority claim
follows. Source-to-Lean identification is not itself a kernel-checked fact.
