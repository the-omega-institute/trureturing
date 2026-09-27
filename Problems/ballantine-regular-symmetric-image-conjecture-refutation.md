---
slug: ballantine-regular-symmetric-image-conjecture-refutation
bibkey: ballantine2024elementary
doi: 10.48550/arXiv.2409.11268
url: https://arxiv.org/abs/2409.11268v3
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.result
---

# Refutation of the regular elementary symmetric image table

## Problem

Ballantine, Beck, Merca and Sagan, arXiv:2409.11268v3, Section 5,
Conjecture 16 (printed page 19), state:

> The value of r_{d,2}(n) - r_{d,3}(n) for d = 2, 3, 4, and 5 are
> shown in the columns of the following table. These values depend on the
> congruence class of n modulo 2, 6, 4, and 10, respectively. The first
> column of the table gives the congruence class for n.

Here `pre_k(lambda)` is the partition whose parts are the products indexed by
the `k`-element position subsets of the parts of `lambda`. The set
`ImP_k(n)` is the image of the partitions of `n` having at least `k` parts,
with equal images counted once. The value `r_{d,k}(n)` counts the members of
that image having no part divisible by `d`.

For `d = 5` and `n` congruent to 4 modulo 10, the printed table gives
`3 floor(n/10) + 1`. Thus its entry at `n = 4` is one.

## Motivation

The conjecture is a universal residue-class table for four regular-image
count differences. A single exact image enumeration whose difference does
not equal its printed cell refutes the full table while retaining the
paper's definitions and its set semantics for repeated images.

## Gap

Preregistration issue #8751 records the source and bounded literature search.
The arXiv versions v1, v2 and v3 were checked; v3, dated October 25, 2024,
retains Conjecture 16 and has no journal reference. Six later arXiv papers
returned by the title search were checked for `Conjecture 16` and `regular`,
with no resolution found. Semantic Scholar returned HTTP 429, and Google
Scholar was not checked. The search therefore does not establish exhaustive
literature coverage or publication priority.

## Route

There are five partitions of four. Enumerating their degree-two and
degree-three elementary symmetric images gives

```text
ImP_2(4) = {(3), (4), (2,2,1), (1,1,1,1,1,1)}
ImP_3(4) = {(2), (1,1,1,1)}.
```

Every displayed image is 5-regular. Consequently `r_{5,2}(4) = 4` and
`r_{5,3}(4) = 2`, so their integer difference is two. The table gives one,
and the universal claim is false.

The Lean proof obtains completeness of the five-partition enumeration from
`Nat.Partition.ofComposition_surj` and `composition_card`, then checks the
two finite image sets and their regularity before specializing the claim at
`d = 5`, `n = 4`.

## Falsifier

The refutation would fail if the five listed partitions were not exhaustive,
if either image set differed from the displayed set under position-counted
elementary symmetric products, if one of the six displayed images contained
a part divisible by five, or if the residue-four entry of the printed
`d = 5` column were not one. The formal result checks each of these links.

## Evidence

- Lean module:
  `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.lean`.
- Resolution theorem:
  `D5/S1/Recurrence/Partitions/BallantineRegularSymmetricImageRefutation.result`.
- Freeze event:
  `sha256:f05175ddeb845e9b19c0a347242aac1e6c620d5e1697cad51e7be1eb399b5bfa`.
- Module statement identity:
  `sha256:56ccf6fd51f5e1397002bb7e1168e43122acc053720e7824042aa4a9b9aca362`.
- Result declaration identity:
  `sha256:e3de94521c75dedd753862e46d416d31dbcac67bea474c9bd8b65b0f9a277eb5`.
- `proof_shape: bind-only`; `escape_witness: none`;
  `admission_basis: open-problem-resolution (issue #8751)`.
- The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.

## Triage

`theorem`. The certified instance at `d = 5`, `n = 4` refutes the universal
table. It does not propose corrected formulas for this column or for the
other three columns.

## ASSUMED-UNVERIFIED

Semantic Scholar coverage, Google Scholar coverage, exhaustive literature
coverage, and publication priority are `ASSUMED-UNVERIFIED`. No claim is
made here that the displayed instance is the least counterexample.
