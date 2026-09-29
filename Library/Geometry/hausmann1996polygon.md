---
bibkey: hausmann1996polygon
authors: Jean-Claude Hausmann and Allen Knutson
year: 1996
title: Polygon spaces and Grassmannians
doi: 10.48550/arXiv.dg-ga/9602012
url: https://arxiv.org/abs/dg-ga/9602012v1
claim: Corollary (4.2) identifies the attainable planar polygon side lengths of perimeter two with the hypersimplex; rescaling gives the balanced-length closure criterion for positive perimeter, while total-zero and empty families have the direct zero-vector realization.
strata_touched:
  - D5/S3/Geometry/Polygons/BalancedPlanarClosure
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Geometry/hausmann1996polygon -->
# Planar closure from the polygon-length hypersimplex

## Source and exact location

Hausmann and Knutson, *Polygon spaces and Grassmannians*, arXiv:dg-ga/9602012v1,
submitted 29 February 1996 (the manuscript title page is dated July 1995).
The cited year is the arXiv submission year, not a journal-publication claim.
Primary text: https://arxiv.org/pdf/dg-ga/9602012v1.

Corollary (4.2), manuscript page 10, gives the image as

\[
\Xi_m=\{(\alpha_1,\ldots,\alpha_m):0\leq\alpha_i\leq1,
\quad\sum_i\alpha_i=2\}.
\]

Its proof explicitly constructs a section of the side-length map into the
planar polygon space. Thus it supplies planar existence, not only spatial
existence. The authors also cite earlier proofs; this note makes no priority
or earliest-source claim and does not independently attest those references.

Section (2.1), page 3, defines polygons as finite ordered vectors summing to
zero, with positive integer edge count. Only *proper* polygons require every
edge to be nonzero. Sections (2.3)–(2.4), pages 3–4, retain zero-edge strata
and normalize nonzero configurations to perimeter 2. Section 4, page 9,
allows nonnegative lengths. Neither strict balance, simplicity, nor genericity
is a hypothesis of Corollary (4.2); its proof explicitly allows a collinear
triangle. Equality and zero-edge boundary points are therefore included.

## Relation to the Lean statement and its degeneracies

For total length \(S=\sum_i L_i>0\), set \(\alpha_i=2L_i/S\).
Nonnegativity and \(2L_i\leq S\) place this vector in \(\Xi_m\).
Choose a planar representative supplied by the source and multiply its edge
vectors by \(S/2\), identifying the Euclidean plane with \(\mathbb C\).
This gives exactly the required norms and zero sum. Conversely, closure
implies each edge length is at most the sum of the others by the triangle
inequality; the Lean public theorem only asserts the existence direction.

The source's perimeter normalization excludes the all-zero configuration,
and its positive edge count excludes the empty family. For \(S=0\), finite
nonnegative lengths are all zero, so the zero-vector family realizes them;
this also handles the empty family. For one edge balance forces this case;
for two edges balance forces equal lengths, realized by opposite real
vectors. These direct boundary constructions and the rescaling are the
explicit bridge to the repository's full scope, not a claim that its statement
appears verbatim in the paper. When a positive edge equals the sum of the
others, taking that edge in one real direction and all others in the opposite
direction also gives a collinear realization directly.

The repository independently formalizes the classical existence criterion
using an attainable-resultant induction and continuity on a complex circle.
This note attributes the criterion, not that exact proof implementation or
every auxiliary resultant claim, and makes no mathematical novelty claim.

## Verified locator

DOI: 10.48550/arXiv.dg-ga/9602012

URL: https://arxiv.org/abs/dg-ga/9602012v1

The cited source is *Polygon spaces and Grassmannians* by Jean-Claude
Hausmann and Allen Knutson. The locator scope is Corollary (4.2), manuscript
page 10, together with the perimeter and polygon conventions in Sections
2.1, 2.3–2.4, and 4 described above.
