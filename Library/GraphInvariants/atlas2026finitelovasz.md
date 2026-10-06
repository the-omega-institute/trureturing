---
bibkey: atlas2026finitelovasz
authors: ATLAS contributors; AutoformBot
year: 2026
title: "ATLAS finite symmetric Lovasz local lemma"
doi: null
url: https://github.com/facebookresearch/atlas-lean/blob/0b121a198307b6153181f5a1d9145dcda2f7bfee/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean
claim: "Finite real probability weights with a dependency graph satisfy the symmetric local lemma under exp(1) p (d+1) at most one."
strata_touched:
  - D5/S3/Combinatorics/Probability/FiniteLovaszLocalLemma
license: Apache-2.0
triage: anchor
---

# A finite symmetric local lemma in Lean

The ATLAS source proves
`MathlibExt.Probability.Combinatorics.LovaszLocalLemma.lovasz_local_lemma_symmetric_finite`.
A finite sample space carries nonnegative real weights summing to one. Bad events
have probability at most a nonnegative real number `p`. A finite simple dependency
graph has maximum degree at most `d`; each event is independent of every joint
intersection of events outside its closed neighborhood. Under
`Real.exp 1 * p * (d + 1) ≤ 1`, avoiding all bad events has positive probability.
Pairwise independence alone does not meet its hypotheses.

## Verified locator

https://github.com/facebookresearch/atlas-lean/blob/0b121a198307b6153181f5a1d9145dcda2f7bfee/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean

The immutable source is in the repository root package, outside the separately
licensed `v1/` archive. The pinned root README attributes the project to
AutoformBot. Adam Kiezun is the author of the first source commit
`c02ba6a03bbf31038201c99963224e76f89d31a3`; the source has no individual proof-author
header, so that commit metadata is not treated as sole mathematical authorship.
The full root license, including its intended-use preface, is retained verbatim
at `docs/reports/lovasz-suppliers/atlas-LICENSE.txt`. The pinned tree contains no
NOTICE file.

## Reused scope and compatibility

All 23 authored source declarations belong to the proof dependency closure of
the public local lemma, including the private finite-probability helpers. The
transplant preserves their proof bodies. The source pin uses Lean `v4.34.1` and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; the consuming pin uses Lean
`v4.33.0` and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
Compatibility removes module/public-section wrappers and replaces the conditional
reduction names `ite_eq_left` and `ite_eq_right` by `if_pos` and `if_neg`.
The transplant is retired when the consuming project's pinned Mathlib supplies
an equivalent finite symmetric local lemma, and consumers then apply that
result directly.

## Mathematical sources

The source cites Noga Alon and Joel H. Spencer, *The Probabilistic Method*,
third edition, Wiley, 2008, Corollary 5.1.2, for the exponential symmetric
criterion. This book attribution is supplied by the formal source; the book
text is not used as an independently inspected proof source here.

The original local lemma is due to Paul Erdos and Laszlo Lovasz,
*Problems and results on 3-chromatic hypergraphs and some related questions*,
Infinite and Finite Sets, Colloquia Mathematica Societatis Janos Bolyai 10
(1975), 609-627. Its Lemma 2 uses the earlier sufficient estimate `4 p d ≤ 1`.
Its polychromatic application is recorded separately in
`erdoslovasz1975polychromatic.md`.
