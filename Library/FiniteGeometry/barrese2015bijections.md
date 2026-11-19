---
bibkey: barrese2015bijections
authors: Kenneth Barrese, Nicholas Loehr, Jeffrey Remmel, Bruce E. Sagan
year: 2015
title: "Bijections on m-level Rook Placements"
doi: 10.1016/j.ejc.2016.03.005
url: https://arxiv.org/abs/1508.05944v1
claim: "Theorem 26 factors the level rook polynomial for arbitrary Ferrers boards. Section 6.2 asks for the number of all boards in a given equivalence class."
strata_touched:
  - D5/S3/Combinatorics/Partitions/RookAugmentedLevels
  - D5/S3/Combinatorics/Partitions/RookClassCandidate
license: citation-only
triage: anchor
---

# Factorization and the whole-class enumeration question

## Verified locator

The preprint is https://arxiv.org/abs/1508.05944v1. The journal article appeared in
*European Journal of Combinatorics* 57, 13–35, DOI 10.1016/j.ejc.2016.03.005.
The numbering and wording below follow the preprint.

## Source scope

Definition 4 lists the nonempty level totals from top to bottom. Section 4.1 aligns
boards at the lower right and permits leading empty columns. For a board of width
$n$ with $s$ nonempty levels, Theorem 26 allows any $N\ge\max(n,s)$.
At $x=mt$ its $m$-falling factorial of length $j$ becomes $m^j$ times the
ordinary falling factorial of $t$. Each product factor becomes a padded
top-down level total plus $mt-mi$ at zero-based position $i$. [§6.1, Theorem 26](https://arxiv.org/html/1508.05944v1#S6.SS1)

The first question in §6.2 asks to count an entire equivalence class. The following
sentence asks for the fixed ordered-level fiber of a singleton board. A formula for
one such fiber supplies a weight in the whole-class sum. The root-vector
admissibility criterion used to index the sum is Proposition 4.4 of the earlier
paper *m-level rook placements*. [§6.2](https://arxiv.org/html/1508.05944v1#S6.SS2) · [Proposition 4.4](https://arxiv.org/html/1308.4081v1#S4)
