---
bibkey: hughes2026radolastexception
authors: Tyler B. Hughes and research agents
year: 2026
title: "The Last Exception for Two-Colour Rado Numbers"
doi: null
url: https://github.com/the-omega-institute/mathdiscoveries/tree/82a9a73903a9f68b476818a37e20b10405aa8b53
claim: "For every k >= 3, the explicit c*(k) is the last boundary for the two-colour lower bound: every valid c > c*(k) has Rado number LB(c,k), while [1,LB(c*(k),k)] has an avoiding colouring."
strata_touched:
  - D5/S3/Combinatorics/ArithmeticRamsey/RadoLastBoundary
  - D5/S3/Combinatorics/ArithmeticRamsey/RadoLastException
license: Apache-2.0
triage: anchor
---

<!-- GID: D5/L/Combinatorics/hughes2026radolastexception -->

# The last exception for two-colour Rado numbers

## Verified primary sources

The formal source is the immutable public revision
[mathdiscoveries@82a9a73903a9f68b476818a37e20b10405aa8b53](https://github.com/the-omega-institute/mathdiscoveries/tree/82a9a73903a9f68b476818a37e20b10405aa8b53),
with the corresponding Lean Pool aggregation at
[lean-pool@623ba6c3c0026e133cf4f](https://github.com/leanprover-community/lean-pool/tree/623ba6c3c0026e133cf4f).
The ported files are pure Lean 4 and retain the source proof structure. The
source reports no human referee; no originality or open-problem-resolution
claim is made here.

Kim, Song, and Hwang, “Rado numbers for the equation x + y + c = kz,”
*Discrete Mathematics* 346 (2023), article 113597,
[doi:10.1016/j.disc.2023.113597](https://doi.org/10.1016/j.disc.2023.113597),
is the verified bibliographic source for the surrounding Rado-number problem.
Martinelli and Schaal, *Ars Combinatoria* 85 (2007), 33–42, Lemma 2, are
credited for the lower-bound formula in the formal source. The upper reflection
argument and the explicit boundary colouring are credited to Tyler B. Hughes.

## Formal statement and scope

For `k >= 3`, `LB(c,k)` is the natural-number lower-bound expression and
`cstar(k)` is the odd/even piecewise formula in the Lean source. If `c` is
valid (`k` odd or `c` even) and `c > cstar(k)`, the source proves
`IsRado(c,k,LB(c,k))`, including forcing at the endpoint and non-forcing below
it. At the boundary it proves an explicit colouring of
`[1,LB(cstar(k),k)]` with no monochromatic solution. Repeated variables are
allowed by the quantified equation. The formal result does not assert finite
existence of a boundary Rado number, a negative-`c` classification, or a
finite-boundary existence theorem.

The lower half uses the residue colouring for odd `k` and the two-block colouring
for even `k`; the upper half uses least-colour-change propagation and reflection
of the equation `x + y = k z + b`. The public source and the ported proof are
kept as attribution and provenance; this note does not claim a literature-priority
result for the formalization.

## Licensing

The ported files are released under Apache License 2.0. The full source license
and the applicable Lean Pool aggregation notice are retained in
`docs/reports/licenses/rado-numbers-last-exception-LICENSE.txt` and
`docs/reports/licenses/rado-numbers-last-exception-NOTICE.txt`.
