---
bibkey: chen2026combinatorialrigidity
authors: Bryan Gin-ge Chen
year: 2026
title: CombinatorialRigidity, source revision 021c2284bc387efee3c3b20a18eb5f769638b578
doi: null
url: https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578
claim: Credited Lean proofs of Laman sparsity and repair, geometric Henneberg preservation, and real planar rigidity with spanning Laman extraction.
strata_touched:
  - D5/S3/Combinatorics/Graph/Laman/SparseSets
  - D5/S3/Combinatorics/Graph/Laman/SafeRepair
  - D5/S3/Combinatorics/Graph/Laman/Moves
  - D5/S3/Combinatorics/Graph/Laman/Framework
  - D5/S3/Combinatorics/Graph/Laman/HennebergRigidity
  - D5/S3/Combinatorics/Graph/Laman/TrivialMotions
  - D5/S3/Combinatorics/Graph/Laman/PlanarForward
  - D5/S3/Combinatorics/Graph/Laman/PlanarRows
  - D5/S3/Combinatorics/Graph/Laman/PlanarLaman
license: Apache-2.0
triage: anchor
---

<!-- GID: D5/L/Geometry/chen2026combinatorialrigidity -->

# Combinatorial rigidity proof source

The source declarations in EdgesIn, Sparsity, Laman, Henneberg and HennebergReverse establish the combinatorial repair and preservation ingredients. Framework, HennebergRigidity, TrivialMotions, the selected RigidityMatroid proofs and LamanTheorem establish the real planar placement characterization. The retained rigidity predicate means existence of a placement whose true edge inner-product map has kernel dimension at most three; it adds no algebraic genericity or graph planarity assumption. The source also supplies consumed dual-space, determinant and Vandermonde identities.

The complete finite-history characterization is a receiving composition of the combinatorial ingredients by cardinal induction and a finite relation chain. The geometric forward induction and same-vertex independent-row converse are credited source ports of LamanTheorem.

The port preserves original copyright and author headers. The complete license, source mapping and receiver-pin retirement condition are in `docs/reports/licenses/laman-henneberg/`.

## Verified locator

https://github.com/bryangingechen/CombinatorialRigidity/tree/021c2284bc387efee3c3b20a18eb5f769638b578
