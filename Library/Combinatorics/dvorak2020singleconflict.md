---
bibkey: dvorak2020singleconflict
authors: "Zdeněk Dvořák; Louis Esperet; Ross J. Kang; Kenta Ozeki"
year: 2020
title: "Single-conflict colouring"
doi: 10.48550/arXiv.1803.10962
url: https://arxiv.org/abs/1803.10962v2
claim: "A local edge assignment forbids one ordered pair of endpoint colours; multiple conflicts on one vertex pair are represented by parallel edges."
strata_touched: []
license: citation-only
triage: anchor
---

# Ordered colour conflicts

The inspected primary text is arXiv:1803.10962v2, deposited 9 October
2020. Section 1, printed page 2, defines a local colour assignment on
each end of every multigraph edge. A permitted vertex colouring must
avoid choosing both endpoint colours specified by any edge. A list of
several forbidden ordered pairs is represented by parallel edges.

For prime-coordinate avoidance, a vertex represents a prime and a colour
represents a permitted first residue. A selected forbidden residue pair
is exactly such an edge conflict. Local alphabets can be relabelled;
their unequal prime sizes and the higher prime-power prefixes require
the separate arithmetic argument in the covering report. This note
attests the conflict model, not that argument or a universal existence
theorem for its arithmetic inputs.

No source text is vendored. No Lean declaration is attributed to this
paper by this note.
