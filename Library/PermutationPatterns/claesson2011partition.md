---
bibkey: claesson2011partition
authors: Anders Claesson, Mark Dukes, Martina Kubitzke
year: 2011
title: "Partition and composition matrices"
doi: 10.48550/arXiv.1006.1312
url: https://arxiv.org/abs/1006.1312v2
claim: "Theorem 3: Lambda is a bijection from inversion tables to partition matrices, with inverse K."
strata_touched:
  - D5/S3/Combinatorics/PartitionMatrix/ChernFuImage
license: citation-only
triage: anchor
---

# Claesson, Dukes and Kubitzke, partition and composition matrices

Journal of Combinatorial Theory, Series A 118 (2011), 1624–1637;
arXiv:1006.1312v2. Definition 2 and Section 2, Theorem 3, on journal page 1626,
give the partition-matrix correspondence.

For A(e) = {y_1 < ... < y_k}, with y_(k+1) = n, the reconstruction has cell
(r,c) equal to {t : e_t = y_r and y_c < t <= y_(c+1)}.
The inverse K at label t is the least label of the column indexed by row(t),
minus one. In each column c, labels form the interval
{y_c + 1,...,y_(c+1)}. Its cardinality is y_(c+1) - y_c, so sums of preceding
column cardinalities telescope to y_r. Thus this K is exactly the fixed Pi
used by Chern and Fu.

Definition 2 uses col(a) < col(b) implies a < b. For distinct labels this is
equivalent to the weakly increasing column-index condition of Chern--Fu
Definition 1.1: either failure contradicts the other implication after
interchanging the two labels.

The Lean reconstruction proves matrix validity and the fixed-map identity
from inversion bounds, and the native coordinate correspondence preserves
all set entries. The literature theorem is not an added axiom or an imported
unverified premise.

The arXiv source has the nonexclusive distribution license. It is used as
mathematical literature, not as software. No third-party code is copied.

## Verified locator

DOI: 10.48550/arXiv.1006.1312; versioned source: https://arxiv.org/abs/1006.1312v2.
