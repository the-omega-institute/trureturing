---
bibkey: erdos1961ginzburgziv
authors: P. Erdős; A. Ginzburg; A. Ziv
year: 1961
doi: null
title: Theorem in the additive number theory
url: https://users.renyi.hu/~p_erdos/1961-25.pdf
claim: The final paragraph states that any sequence of 2n-1 elements of an abelian group of order n contains n terms with product the identity; repeated extraction gives exact zero-sum block partitions of zero-sum labeled supports of size mn.
strata_touched:
  - D5/S3/FiniteGroups/Aliabadi/AbelianZeroSumPartition
license: citation-only
triage: anchor
---

# Theorem in the additive number theory

P. Erdős, A. Ginzburg and A. Ziv, *Bulletin of the Research Council of
Israel, Section F: Mathematics and Physics*, **10F1** (1961), 41–43.
The [author-hosted primary article](https://users.renyi.hu/~p_erdos/1961-25.pdf)
is cited without redistributing its PDF.

The final paragraph states the extension from integers modulo n to every
abelian group of order n. In additive notation, among any 2n−1 entries one
can select n entries summing to zero. Entries need not have distinct values.
The Lean statement allows a larger finite support by retaining a subset
of the required size and keeps the original labels throughout.

The product step first selects 2q−1 disjoint n-element blocks with zero
sum in the first factor, then applies extraction in the second factor to
the second-coordinate sums of those same blocks. The union of the q
selected blocks has nq labels and zero sum in both factors. The cyclic
case is supplied directly by pinned Mathlib, and the finite abelian
presentation is supplied by the existing Gordon module.

The exact partition is an iterated consequence: remove zero-sum blocks
of size n until one block remains. Its sum is zero because the initial
total and all removed block sums are zero. The result supplies a function
from Fin m to finite subsets of the original label type, with pairwise
disjoint blocks and union exactly the original support. Empty supports,
m=0, and the trivial group are included. These are literature-known
mathematical results; no originality is claimed.
