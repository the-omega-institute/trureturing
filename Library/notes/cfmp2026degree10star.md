---
bibkey: cfmp2026degree10star
authors: trureturing contributors
year: 2026
title: An explicit degree-ten high edge in a three-star packet
doi: null
url: pending PR from dev
claim: Paper proof of one explicit orientable three-star degree-eight packet triangulation with high degrees 10 and 38, realized by a heterogeneous shared-edge co-volume box.
license: citation-only
triage: anchor
strata_touched: []
---

The proof and pairing table are in `docs/develop/theory/CFMP_DEGREE10_STAR.md`.
This is outside the previous three-edge degree-eight/high-at-least-twelve
result: six degree-eight global classes remain a three-star in every
16-tetrahedron, while the other classes have degrees ten and 38.

The global cosh box is [11/8,2] on degree-eight edges, [11/10,71/50] on the
degree-ten edge, and [1009/1000,21/20] on degree-38 edges. Exact endpoint
squares are checked by `verify_degree10_star.py` and
`audit_degree10_bounds.py`. Degree-eight cosine bounds are 143/200 below and
35941/50941 above. Degree-ten upper endpoint is
19195*sqrt(880915135)/704732108, whose square is
1842240125/2818928432 < cos(pi/5)^2. For degree 38, the two actual high/low coordinate patterns have the same
relaxed upper endpoint 4489*sqrt(8216635)/13146616, with square
100755605/105172928 < cos(pi/19)^2; the lower endpoint uses
1982/2009 > cos(pi/19) via rational Taylor bounds.

The generalized incidence condition is: every degree-ten occurrence has at
least one high neighbour of degree at least 38; its other high neighbour may
have degree 10 or at least 38. The explicit example has six degree-ten
occurrences with two degree-38 neighbours and four with one degree-10 and one
degree-38 neighbour.

The finite topology verifier checks coherent orientation, one circular edge
link per edge class, no reversed edge, six degree-eight classes, the degree
ten incidence placement, and vertex links (16,6,-2),(48,10,-14). The endpoint
verifier enumerates all formula-coordinate stabilizers exactly with rational
squares.

This is a restricted explicit realization theorem, not arbitrary minimum-eight
CFMP, and does not claim a general degree-ten packet criterion.
