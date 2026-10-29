---
bibkey: kagey2023rectangulartorus
authors: Peter Kagey; William Keehn
year: 2023
title: "Counting tilings of the n x m grid, cylinder, and torus"
doi: null
url: https://arxiv.org/abs/2311.13072v1
claim: "Conjecture 5.1.1: a rectangular-torus plane tiling fixed by a translated transposing right action is equivalent to a gcd-square torus tiling."
strata_touched:
  - D5/S3/Combinatorics/KageyKeehnRectangularTorus
license: citation-only
triage: anchor
---

# Rectangular tori under transposing actions

Peter Kagey and William Keehn's paper defines grid, torus, decorated tile-design, and right dihedral actions, including cyclic translations. Section 5.1, Conjecture 5.1.1 asks whether a plane tiling represented by an n x m torus and fixed under `(a,b,r)`, `(a,b,r^3)`, `(a,b,rf)`, or `(a,b,r^3f)` is equivalent to a gcd(n,m) x gcd(n,m) torus tiling. The journal version carries the same statement as Section 6.1, Conjecture 42.

The source uses right actions on cells and on designs. Its operational linear maps are `r : (x,y) ↦ (-y,x)`, `r^3 : (x,y) ↦ (y,-x)`, `rf : (x,y) ↦ (y,x)`, and `r^3f : (x,y) ↦ (-y,-x)`, with the label action `d ↦ d·h`. The conjugation coordinate map used in the source's action bookkeeping is the inverse linear map; it must not be identified with the operational cell map. On a q by q representative the corresponding center constants are `(q-1,0)`, `(0,q-1)`, `(0,0)`, and `(q-1,q-1)`. For unequal dimensions the statement concerns the represented periodic plane and does not assign a D8 action to the finite rectangle itself.

The formal source keeps arbitrary tile types and decorations, the literal integer-plane lift, right-action signed coordinate maps, all translations and affine center constants, and pointwise equality of the resulting decorated plane. It proves existence of the gcd-square presentation without asserting minimality. The canonical Lean constructor labels are explicitly mapped to the source labels in the Blueprint Scribe: source `r` uses internal `.r3`, source `r^3` uses `.r`, and the two reflection labels retain `.rf` and `.r3f`.

## Verified locator

Source: https://arxiv.org/abs/2311.13072v1

Section 5.1, subsection “Rectangular tori under 90 degree rotation”, Conjecture 5.1.1. The source TeX gives the four alternatives and the gcd-square conclusion. The journal alias is JIS 27 (2024), 24.6.1, Section 6.1, Conjecture 42.
