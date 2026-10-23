---
bibkey: fokkinkrust2024splythoff
authors: Robbert Fokkink; Dan Rust
year: 2024
title: "Queen reflections: a modification of Wythoff Nim"
doi: 10.1007/s00182-022-00824-1
url: https://arxiv.org/abs/1904.08339
claim: Section 9 asks whether every Splythoff Nim row and column contains each Sprague-Grundy value exactly once.
strata_touched:
  - D5/S0/Certificates/Games/SplythoffGrundyRows
license: citation-only
triage: anchor
---

# Splythoff Nim and its Sprague–Grundy rows

## Verified locator

DOI: https://doi.org/10.1007/s00182-022-00824-1

Source: https://arxiv.org/abs/1904.08339

Version: https://arxiv.org/pdf/1904.08339v2, Section 9, printed page 16.
The journal article is in International Journal of Game Theory 53, 1099–1117.

## Source statement

> For Splythoff Nim, it appears that every row or column contains each Sprague-Grundy value once and no more. We do not have a proof for that.

This is the complete row/column remark on printed page 16 of arXiv v2.
Positions are ordered pairs of natural pile sizes, including zero. A single
move reduces one pile; a double move removes the same positive number
from both piles. Section 2 states:

> We modify Wythoff Nim by allowing the additional option of a split. If a player takes an equal number of counters from both piles and only one pile remains, then he can split the remaining pile into two.

> A split is only allowed after taking counters from both piles. It is not allowed to take all counters from a single pile and then split.

For a split, the smaller positive pile is removed and the remaining
counters are distributed between the two piles. Thus from `(x,y)` it
reaches any `(c,d)` with `c+d = max(x,y)-min(x,y)` when `min(x,y) ≥ 1`.
The Sprague–Grundy value is the least natural number absent from all
follower values.

## Scope

The repository proof establishes the quoted row/column statement and the
bound `y ≤ 5x+2g+3` for the occurrence of value `g` in row `x`. The source's
separate remark on reflected diagonals remains open. Its results on
losing positions and Tribonacci encodings are not premises of this proof.

Ortega's MSc thesis on losing positions is ASSUMED-UNVERIFIED: its full
text was inaccessible (HTTP 403; Firecrawl HTTP 402). No exhaustive
prior-art clearance or claim of original priority is made.
