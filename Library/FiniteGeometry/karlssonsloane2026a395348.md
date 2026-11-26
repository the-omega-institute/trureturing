---
bibkey: karlssonsloane2026a395348
authors: Jonas Karlsson and N. J. A. Sloane
year: 2026
title: "OEIS A395348 and Rahid Zaman’s spiral-queens recurrence"
doi: null
url: https://oeis.org/A395348
claim: "Rahid Zaman conjectures that the Black labels satisfy a(n+4) = a(n) + 8*n + 34 for every n >= 2."
strata_touched:
  - D5/S3/Combinatorics/Polyomino/SquareSpiralShells
  - D5/S3/Combinatorics/Polyomino/OeisA395348FourLag
license: citation-only
triage: anchor
---

# OEIS A395348 and Rahid Zaman’s recurrence

## Verified locator

The OEIS A395348 entry credits the sequence to Jonas Karlsson and N. J. A. Sloane
and the recurrence conjecture to Rahid Zaman. The NAME and FORMULA fields are
unpaginated. [Pinned OEIS entry](https://raw.githubusercontent.com/oeis/oeisdata/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq/A395/A395348.seq)

> Conjecture: a(n+4) = a(n) + 8*n + 34 for n>=2.

The offset is zero. The origin has label zero. The spiral runs east, north,
west and south with leg lengths 1, 1, 2, 2, and so on. Black moves first. At
each turn the mover selects the least unoccupied label whose cell shares no
row, column or diagonal with any opposing queen already placed. The paired
entry records Red's labels. [A395349](https://oeis.org/A395349)

Michael S. Branicky's generator uses a separate increasing cursor for each
color. Earlier rejected labels remain forbidden by persistent occupancy or
opposing attacks. Each previously accepted label remains occupied. The
cursor therefore has the same selection rule as search from zero.
[A395348 and A395349 generator](https://oeis.org/A395348/a395348.py.txt)

The bounded literature search is recorded in the preregistration. Literature
coverage beyond that search is ASSUMED-UNVERIFIED.
[Issue #34447](https://github.com/the-omega-institute/trureturing/issues/34447)
