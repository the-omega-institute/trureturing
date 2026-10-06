---
bibkey: bogdanov2020xortriangle
authors: Ilya Bogdanov
year: 2020
title: "Answer to Number triangle"
doi: null
url: https://mathoverflow.net/a/359278
claim: "For each fixed row length over the two-element field, the clockwise top-row-to-right-edge map has third iterate equal to the identity."
strata_touched:
  - D5/S3/Combinatorics/XorTriangle/ValueOne
license: CC-BY-SA-4.0
triage: anchor
---

# Bogdanov, reversible XOR triangles

MathOverflow answer 359278, revision 5, studies the clockwise side map of a
fixed-length binary XOR triangle. The relation between three incident bits
is symmetric over the two-element field. Rotating the triangle preserves
this relation, and three successive side changes recover the original row.
The statement retains every position at the fixed row length.

This is literature support for reversible-triangle reasoning, rather than
an explicit settlement of Kagey's selected value-one conjecture. The Lean
module proves the needed edge injectivity locally by backward reconstruction
and uses no literature axiom. It contains no separate side-map cube theorem.

The reversible-triangle argument is adapted from Ilya Bogdanov's answer,
attributed under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
The adaptation is the local reconstruction argument used in the value-one
proof; the MathOverflow answer is not a kernel-verified supplier.

## Verified locator

- Source: https://mathoverflow.net/a/359278, revision 5.
- Revision identity: `E8608C9B-A5DF-4521-A836-A6DFF07C6CD4`.
- Scope: fixed-length clockwise side map and its threefold composition.
