---
bibkey: codex2026rectangulardeltachain
authors: Codex implementation worker
year: 2026
title: Maximum integer progression length in a rectangular window
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: A sign-selected corner attains one plus the minimum nonzero-coordinate quotient.
strata_touched:
  - D5/S3/Arith/Lattices/RectangularDeltaChain
license: citation-only
triage: anchor
---

# Rectangular integer progressions

This note records a repository derivation of the elementary maximum-length formula.
For a finite coordinate set, natural side lengths L, and an integer direction with an
explicitly nonzero coordinate, the largest point count is one plus the minimum of
L(p) divided by the absolute direction component, rounded down, over moving coordinates.

## Verified locator

本条**不是文献陈述,是本仓推导**,故 `doi: null`。规范定位是仓库本身:
https://github.com/the-omega-institute/trureturing
形式化真源为 `D5/S3/Arith/Lattices/RectangularDeltaChain.lean`，
公开定理 `longest_chain_length`；`corner_chain` 给出达到该长度的显式角点构造。

The construction starts at L(p) when the direction is negative, and at zero otherwise.
At every permitted index the displacement magnitude fits within each coordinate width.
Conversely the first and last chain points in any moving coordinate differ by
(n−1) times the absolute direction component, yielding the coordinate quotient bound.
The zero direction admits sequences of arbitrary length.

The search and verification scope is recorded in
`docs/reports/deltachainwindow/preregistration.md` and the accompanying result report.
This is an elementary general proof, with no claim of a new mathematical discovery.
