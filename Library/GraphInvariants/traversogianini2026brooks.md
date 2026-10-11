---
bibkey: traversogianini2026brooks
authors: Juan Pablo Traverso Gianini
year: 2026
title: "BrooksSubcubic: finite subcubic four-clique-free graph coloring"
doi: null
url: https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic
claim: "Every finite simple graph with maximum degree at most three and no four-clique is three-colorable."
strata_touched:
  - D5/S3/Combinatorics/Graph/Brooks/Coloring
  - D5/S3/Combinatorics/Graph/Brooks/Cuts
  - D5/S3/Combinatorics/Graph/Brooks/Endblock
  - D5/S3/Combinatorics/Graph/Brooks/Subcubic
license: Apache-2.0
triage: anchor
---

# Subcubic Brooks theorem: Lean source

Juan Pablo Traverso Gianini's formalization proves
`BrooksSubcubic.brooks_cubic`: for a finite vertex type, a simple graph with
`G.maxDegree ≤ 3` and `G.CliqueFree 4` has `G.Colorable 3`.
Connectedness is not a hypothesis. The theorem is the subcubic specialization
of Brooks' theorem, not a new graph-coloring theorem.

## Verified locator

https://github.com/Vilin97/lean-pool/tree/91c154506e3d08a1a25e4966c22c99212bf9df54/LeanPool/BrooksSubcubic

- Immutable distribution: `Vilin97/lean-pool`, commit
  `91c154506e3d08a1a25e4966c22c99212bf9df54`.
- Exact declaration: `LeanPool/BrooksSubcubic/Main.lean`, lines 28–49.
- Author source recorded in `LeanPool/projects.yml`:
  https://github.com/jtraverso/lean-pool/tree/aced439fd4161d118bf167a1e8d10553f28913fe/LeanPool/BrooksSubcubic.
- Distribution and author-source pins: Lean `v4.35.0-rc3`, Mathlib
  `c55e6e786f49471c72fbddbec5415808896aec1e`.
- Copyright headers name Juan Pablo Traverso Gianini. The full distribution
  `LICENSE` and `NOTICE` are preserved as
  `docs/reports/brooks-suppliers/lean-pool-LICENSE.txt` and
  `docs/reports/brooks-suppliers/lean-pool-NOTICE.txt`.

## Reused scope

The source closure spans `Greedy`, `NonRegular`, `ColouringGlue`,
`ComponentAttachments`, `CandidatePair`, `CutVertex`, `CutPartition`,
`Endblock`, `K4Free`, `NoCutTriple`, `GoodTriple`, `CutColouring`,
`CubicColouring`, and `Main`. Only declarations needed by the local theorem
and its consumers are retained. The local modules group these source units
while preserving their proof text and copyright headers.

Compatibility consists of removing upstream module/public-section wrappers,
redirecting imports, and using the pinned dependent-if reduction names
`dif_pos` and `dif_neg` in place of `dite_eq_left` and `dite_eq_right`.
These transplants are retired when this repository's pinned Mathlib contains
equivalent declarations, with consumers changed to direct applications.

## Mathematical source and boundary

R. L. Brooks, *On colouring the nodes of a network*, Proceedings of the
Cambridge Philosophical Society 37 (1941), 194–197,
DOI https://doi.org/10.1017/S030500410002168X, is the original theorem.
The publisher metadata supplies this bibliographic locator; the original
article text is not used as a checked proof source here.

An accessible statement and proof are in Daniel W. Cranston and Landon Rabern,
*Brooks' theorem and beyond*, https://arxiv.org/abs/1403.0479v1:
page 2 states the theorem and the minimal-counterexample reduction;
page 3 gives the greedy/good-triple proof. The published version is
Journal of Graph Theory 80 (2015), 199–225,
DOI https://doi.org/10.1002/jgt.21847.

A bound on the average degree does not by itself imply the maximum-degree
hypothesis. The hereditary sparsity application additionally needs a
low-degree deletion argument and the degree-sum identity. That interface
reduction is separate from the reused subcubic theorem. The source supplies
neither a Kostochka–Yancey critical-edge estimate nor a covering-system repair
assignment.
