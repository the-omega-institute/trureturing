---
bibkey: razwigderson2019subspace
authors: Orit E. Raz; Avi Wigderson
year: 2019
title: Subspace arrangements, graph rigidity and derandomization through submodular optimization
doi: null
url: https://arxiv.org/abs/1901.09423v1
claim: The span of cuts of a finite subspace family by a hyperplane in general position has dimension equal to the minimum partition sum of uncut block dimensions minus one.
strata_touched:
  - D5/S3/Factorization/Galois/ActualWindowCommonKernel
license: citation-only
triage: anchor
---

# Common hyperplane cuts and partition rank

## Verified locator

Orit E. Raz and Avi Wigderson, *Subspace arrangements, graph rigidity and
derandomization through submodular optimization*, arXiv:1901.09423v1:
https://arxiv.org/abs/1901.09423v1 .

The versioned full text is available at
https://arxiv.org/html/1901.09423v1 .
Definition 5.1 specifies general position; its footnote permits the empty
middle family in condition (ii). Theorem 5.2 gives the partition-rank formula.
Lemma 5.3 and the following induction construct an attaining partition.
Theorem 7.1 separately proves genericity in characteristic zero or sufficiently
large positive characteristic. Definition 2.1 and Corollary 3.2 concern the
unique minimizing partition with the fewest blocks.

## Application and boundary

For a finite family V(i), let T be the span of all V(i) intersected with the
same hyperplane. The proof groups i and j when T+V(i)=T+V(j). Distinct such
extensions intersect in T. The general-position intersection condition gives
independence of the class cut spans by induction. Recursing on the proper
classes and combining their partitions yields the attaining partition.

R5 (31.5)-(31.7) uses block-supported embedding rows. If U(i,sigma) is the
value of the common normal functional on the i-th row, the rows
U(1,sigma)b(i,sigma)-U(i,sigma)b(1,sigma) span the cut whenever
U(1,sigma) is nonzero. A subfamily's uncut span is a direct product over
coordinate blocks, so its dimension is the sum of the block row ranks.

The deterministic implication does not prove genericity of the normal, the
unique fewest-block optimum, descent to an actual intermediate field, or
specialization over the original field. These are distinct inputs to the
full R5 (31.10) inference.
