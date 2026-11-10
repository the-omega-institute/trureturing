---
bibkey: shapiro2026treewords
authors: Boris Shapiro
year: 2026
title: Transposition Cayley Spectra and Subgraph Counts
doi: null
url: https://arxiv.org/abs/2610.14373v1
claim: Conjecture 1(iii) characterizes identity edge words on every finite tree by multiplicity two and vertexwise noncrossing.
strata_touched:
  - D5/S3/Combinatorics/Graph/SupportForestMoments/ShapiroTreeIdentityWords
license: citation-only
triage: anchor
---

## Verified locator

Source: https://arxiv.org/abs/2610.14373v1

Section 4.1, page 14, Conjecture 1(iii):

> For a tree T, a word of length 2|E(T)| in the edges of T using every edge has product 1 if and only if every edge occurs exactly twice and, for every vertex x of T, the subword formed by the edges incident to x is a non-crossing double occurrence word.

The paragraph immediately following the conjecture states:

> Part (iii) implies (i), since for a star the condition says that the double occurrence word is non-crossing; there are Catₑ non-crossing pairings and e! labellings.

## Mathematical scope

Vertices are represented by `Fin n`, with `SimpleGraph.IsTree` for connectedness
and acyclicity. Each unordered edge acts by its endpoint transposition. The word
uses only tree edges, uses every tree edge, and has length twice the number of
edges. Permutation multiplication satisfies `(σ * ρ)(v) = σ(ρ(v))`.
A double occurrence word has two copies of each occurring letter. Noncrossing
excludes alternating positions of two distinct letters and permits nesting.
The one-vertex tree and the empty word are included.

The result concerns part (iii). It supplies the local criterion used in the
source's implication to part (i); no Catalan enumeration, cycle formula,
inversion theorem or reconstruction statement is asserted here.

## Finite verification

The exact experiment is `docs/reports/tree-identity-words/check.py` in
[`the-omega-institute/trureturing-experiments`](https://github.com/the-omega-institute/trureturing-experiments/tree/82686ecf6f80257b272bc14b5d427bb34ccb3ab1/docs/reports/tree-identity-words),
commit `82686ecf6f80257b272bc14b5d427bb34ccb3ab1`.
Its SHA-256 is `1f7bd589e624ef83cc5fec145cea34830c58bace8300fda30d91f935f3e6e16c`.
Command: `python3 docs/reports/tree-identity-words/check.py`; exit code 0,
with final line `ALL_CHECKS_OK`. This bounded computation checks tree shapes
with at most five edges and does not establish the unrestricted theorem.

## Literature boundary

The literature screen recorded in issue #22558 located classical star-factorization
and planar-constellation results, but no explicit settlement of this fixed-tree
criterion in the checked sources. Search completeness and whether an unlocated
corollary already supplies the exact criterion remain ASSUMED-UNVERIFIED.
