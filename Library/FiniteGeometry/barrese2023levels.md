---
bibkey: barrese2023levels
authors: Kenneth Barrese
year: 2023
title: "Weighted File Placements on Singleton Boards"
doi: 10.48550/arXiv.2312.10855
url: https://arxiv.org/abs/2312.10855v1
claim: "Sections 2.2 and 5 ask for the number of all Ferrers boards with prescribed ordered level numbers in the fixed n-column, n-level ambient rectangle."
strata_touched:
  - D5/S3/Combinatorics/Partitions/FerrersLevelCounting
license: citation-only
triage: anchor
---

# Prescribed ordered level numbers

## Verified locator

DOI: 10.48550/arXiv.2312.10855. URL: https://arxiv.org/abs/2312.10855v1. The verified scope is Section 2.2, the ordered level numbers in Theorem 4 and the following open counting question, and the first open question in Section 5. It concerns all Ferrers boards in the fixed n-column, mn-row ambient rectangle, with levels indexed from the top for the prescribed ordered data, including zero columns and empty levels.

The separate 2015 source is Barrese, Loehr, Remmel and Sagan, *Bijections on m-level Rook Placements*, https://arxiv.org/abs/1508.05944v1, Definition 4 in Section 2.2 and the counting question in Section 6.2. Its l-operator fiber ranges over all normalized widths for a prescribed singleton target; zero-padding normalization and the separately declared empty-board extension retain the boundaries stated below.

## Source scope

In Section 2.2 an ambient board has n columns and mn rows, divided into n levels of m rows, counted from the bottom. The ordered level numbers in Theorem 4 and the following open question are instead indexed from the top. The unknown boards in this question are arbitrary Ferrers boards; only other results in the paper require singleton boards. Leading zero columns and empty top levels remain part of this fixed ambient description. Section 5 repeats the counting question as its first open question.

The related question in Barrese, Loehr, Remmel and Sagan, *Bijections on m-level Rook Placements*, arXiv:1508.05944v1, Section 6.2, fixes a singleton board C and asks for all Ferrers boards B with l(B)=C. Definition 4 in Section 2.2 defines l(B) by reversing the bottom-to-top list of nonempty level totals. That formulation has no prescribed input width. The paper uses left zero padding of column tuples elsewhere; normalized shapes under that convention must be distinguished from literal finite subsets of the positive absolute coordinate grid. The empty-board extension of Definition 4 is a separate convention because its largest nonempty level is undefined.

Neither question asks here for the size of a whole m-level rook equivalence class. Gaussian polynomials used to count row configurations are ordinary auxiliary generating polynomials, unrelated to the file-placement weights of the 2023 paper.
