---
bibkey: pemmasani2026blackouts
authors: Arjun Pemmasani
year: 2026
title: "Blackouts Preserving Rectangle Identifiability on Grid Points: A partial solution to Problem 001 of Kagey's Open Problem Collection"
doi: null
url: https://github.com/apemm/Kagey-Problems/blob/b9567e4dc1c7cf1e5034569571a9479b1b83dc57/kagey-problems/problem001/paper/main.tex
claim: "The Three-Row conjecture asserts that the maximum valid blackout in a three-row grid with m columns is m+2 for every m>=3, where every lattice rectangle, including tilted rectangles, must remain identifiable from its visible corner set."
strata_touched:
  - D5/S0/FiniteGeometry/RectangleIdentifiability/ThreeRowBlackoutMaximum
license: "citation-only; no license located for upstream Lean code, which is not copied; OEIS governed by https://oeis.org/LICENSE"
triage: anchor
---

# The Three-Row blackout conjecture

Pemmasani's preliminary note studies Peter Kagey's Problem 001: delete as
many grid points as possible while every rectangle remains identifiable
from its visible vertices. The note's section "Conventions and the
presentation map" fixes unordered corner sets, all nondegenerate Euclidean
rectangles, including squares and tilted rectangles, and permits the empty
presentation. Its "Refuted and live conjectures" section, label
`conj:threerow`, gives the exact target:

> T(3,m) = m+2 for all m >= 3.

The corresponding COMMENTS line in OEIS A397315 repeats this conjecture.
The entry is by Arjun Pemmasani, September 2, 2026. Its additional claim of
verification through width ten is a source claim, not proof evidence used
by the formal theorem.

The note's difference-set/hitting-set criterion and two-row Strip Theorem
are known background. In particular, for at least three columns, two
columns cannot both have the same two rows entirely blacked out: comparing
each with a third column produces equal presentations of different
rectangles. The three-row proof credits this obstruction and proves its
needed finite-set form locally. The exact three-row upper bound also uses
a collision across different row pairs. The two-row theorem by itself
does not give the full three-row target.

## Verified locator

- https://github.com/apemm/Kagey-Problems/blob/b9567e4dc1c7cf1e5034569571a9479b1b83dc57/kagey-problems/problem001/paper/main.tex
- Preliminary-note Git revision:
  `b9567e4dc1c7cf1e5034569571a9479b1b83dc57`, dated
  2026-09-09T06:25:25Z. The complete 18,960-byte TeX has SHA-256
  `a5768b49f620c70e681cacf1ddf12a6771583e1247656ea62f5c08a921892074`.
  The document uses a generated current-date command, so the citation does
  not infer an independently printed publication date.
- https://oeis.org/A397315 and its complete official text at
  https://oeis.org/search?q=id:A397315&fmt=text, revision 38,
  September 12, 2026, 22:10:01; 4,810 bytes, SHA-256
  `14370cb2594daee56b3efcb29387b2ede84684ca73ea32f0e579ef4982d84983`.
- Original general question: https://peterkagey.com/problems/001/.
  This older problem is not described as a newly posed question.

The complete note and OEIS entry were read. The note's blanket numerical
cross-verification wording conflicts with some "engine only" labels; its
older four-row overview and later table also differ. Its five-by-five
diagram legend has a polarity conflict with the OEIS marked positions.
None of these numerical tables or diagrams is used as a certified witness.
The exact named Three-Row conjecture agrees between the inspected sources.

The upstream Lean file uses different pins, and no license was located.
No upstream Lean source is copied or imported. The local proof uses only
pinned Mathlib and credits known mathematical background. Citation of this
source and bounded searches do not establish global priority or exhaustive
absence of a prior settlement.
