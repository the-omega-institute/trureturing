---
bibkey: alekseyev2026halving
authors: Max A. Alekseyev
year: 2026
title: Halving Partitions and Hyperbinary Expansions
doi: null
url: https://arxiv.org/abs/2611.01243v1
claim: "Section 6 asks whether a(n) belongs to a finite family of integer sequences closed under both binary decimations."
strata_touched:
  - D5/S1/Recurrence/Partitions/HalvingPartitionNonregularity
license: citation-only
triage: anchor
---

# Halving partitions and binary regularity

The fixed source is [arXiv:2611.01243v1](https://arxiv.org/html/2611.01243v1),
Definition 1 on PDF page 1 and the regularity question in section 6 on PDF page 18.

Definition 1 counts positive parts whose first part is a lower or upper integer
half of n and whose later parts are lower or upper integer halves of the previous
part. The halves form a value set, so coincident even halves produce one value.
The parts sum to n. The empty partition is the unique halving partition of zero.
The sequence a(n) sums the counts over every finite length.

Section 6 asks:

> This raises the question of whether a(n) is 2-regular: does there exist a finite family of integer sequences containing a(n) such that, for each sequence b(n) in the family, both b(2n) and b(2n+1) are integer linear combinations of sequences in the family [16]?

The formal source carrier stores actual ordered positive lists and the virtual
predecessor n. Repeated entries and terminal ones are retained. The matrix and
family predicates use fixed integral coefficients on every natural input,
including zero. Enumeration of a finite index type does not require independent
constituent sequences or invertible matrices.

The source supplies the definition and question. The dyadic list classification
and cardinality formula have direct repository proofs; the enumerative identity
is also a specialization of Alekseyev's prior fixed-length Theorem 5. The
recurrence obstruction answers the separate regularity question. The
[weighted source](mazhang2026weightedhalving.md) retains the later extensions
and the prior enumeration, dilation and lower-bound attributions.

## Verified locator

- URL: https://arxiv.org/abs/2611.01243v1
- Version and location: arXiv:2611.01243v1, Definition 1 on PDF page 1 and the regularity question in Section 6 on PDF page 18.
