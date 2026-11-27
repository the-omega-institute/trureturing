---
bibkey: cioni2025sorting
authors: Lapo Cioni, Luca Ferrari, Rebecca Smith
year: 2025
title: "Sorting permutations using a pop stack with a bypass"
doi: 10.1016/j.disc.2025.114964
url: https://arxiv.org/abs/2503.08285v1
claim: "Simple permutations sortable by two pop stacks in parallel with bypass are counted by F_{2n-5} - 1 (n odd) and F_{2n-5} (n even)."
strata_touched:
  - D5/S3/Combinatorics/PopStack/PopStackSimple
license: citation-only
triage: anchor
---

# Cioni, Ferrari and Smith, sorting permutations using a pop stack with a bypass

The paper studies permutations sortable by a pop stack whose entries may bypass the stack, and by
several such machines in series and in parallel, determines bases of the sortable classes, and closes with
open problems on their enumeration.

## Verified locator

DOI: 10.1016/j.disc.2025.114964

URL: https://arxiv.org/abs/2503.08285v1

- Locator: Section 9, the permutations sortable by two pop stacks in parallel with bypass form the class
  Av(2341, 25314, 42513, 42531, 45213, 45231, 52314, 642135, 642153).
- Locator: Section 9.2, Conjecture: the number a_n of simple permutations of size n in this class satisfies
  a_0 = a_1 = 1, a_2 = 2, a_n = F_{2n−5} − 1 for odd n ≥ 3 and a_n = F_{2n−5} for even n > 3.

## Reading of the statement

The numbers of simple permutations in the class for n = 0, …, 11 are 1, 1, 2, 0, 2, 4, 13, 33, 89, 232,
610, 1596; the class itself has 1, 1, 2, 6, 23, 97, 418, 1800, 7717, … elements (OEIS A374165).

## Bounded prior-resolution evidence

Read on 2026-10-01 and 2026-10-02: arXiv lists only version 1 of the preprint. The statement appears again as
Conjecture 8 in the authors' contribution to the Permutation Patterns 2025 booklet (July 2025). The abstract
of the published version (Discrete Math. 349(5), 2026) coincides with that of arXiv version 1 and does not
announce an enumeration of the simple sortable permutations; the full text of the published version was not
read. Searches of arXiv, the citation index and GitHub located no later treatment of the conjecture. This is a
bounded negative finding.
