---
bibkey: chu2025toeplitz
authors: Hojin Chu, Homoon Ryu
year: 2025
title: Linear-Time Computation of the Frobenius Normal Form for Symmetric Toeplitz Matrices via Graph-Theoretic Decomposition
doi: null
url: https://arxiv.org/abs/2505.20811v1
claim: A singleton positive Toeplitz step connects precisely the labels with equal residues; the occurring residue classes give the components and their number.
strata_touched:
  - D5/S3/ConceptDynamics/GraphColoring/StepGraphComponentCount
license: citation-only
triage: anchor
---

# Fixed steps and residue components

## Verified locator

The exact upstream locator is:
https://arxiv.org/abs/2505.20811v1

The arXiv record and https://arxiv.org/html/2505.20811v1 were retrieved.
Definition 2.1 specifies adjacency by `|i-j|` belonging to the nonzero
Toeplitz offsets. Definition 3.5 defines residue blocks
`[i]_d = {v in [n] : v congruent to i modulo d}` and their quotient graph.

## Shared source chain and declaration bridges

Specialize the offsets to one positive step m, discard weights and loops,
and relabel the interval from `1,...,d` to `0,...,d-1`. Translation preserves
label differences and permutes residues. If m is outside the interval's
possible differences, the specialized graph has no edges. The following
are standard constructions and direct consequences of this specialization;
the paper's general quotient definition alone is not a connectivity theorem.

- `stepGraph`: a local representation of the standard construction
  (标准构造的本地表示). For m ≥ 1, the symmetrized relation `i+m=j`
  is exactly `|i-j|=m`; `SimpleGraph.fromRel` removes loops.
- `occurringResidues`: a local representation of the standard construction
  (标准构造的本地表示), taking the image of the interval under remainder.
  It retains only nonempty residue blocks, unlike a list of all m residues.
- `reachable_iff_mod_eq`: an edge changes a label by ±m, hence a walk
  preserves its remainder. Conversely, repeatedly subtract m while the
  label is at least m; the intermediate labels remain in the interval and
  end at the remainder. Reverse and concatenate two such walks.
- `componentEquivResidues`: a local representation of the standard quotient
  construction (标准构造的本地表示). The preceding equivalence makes the
  remainder map well-defined on components and injective. Each occurring
  residue has a representative vertex, giving surjectivity.
- `connectedComponent_card`: count through that bijection. An occurring
  remainder is below both m and d; every integer below both occurs as its
  own remainder. Thus the image is `range (min m d)` and its size is
  `min m d`. This includes d=0 and m≥d. The count requires m≥1.

## What this note does and does not attest

Attested by this repository's own retrieval: the record's authors, title,
version, and the displayed definitions in the v1 HTML. The local source
was read to check the interval convention, positivity and construction
bridges above. The paper is not claimed to state these Lean declarations
verbatim, nor to supply a separate theorem with all their edge cases.

The round-19 classification in issue #6298 is received as the task's settled
classification. Any claim that this is the earliest source, or that the
paper was checked in its entirety, remains `ASSUMED-UNVERIFIED`; neither
claim is needed for the displayed source chain.
