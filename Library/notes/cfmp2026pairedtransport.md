---
bibkey: cfmp2026pairedtransport
authors: trureturing contributors
year: 2026
title: Sources for transverse-pair transport and protected multi-reservoir realization
doi: null
url: https://github.com/the-omega-institute/trureturing/pull/9474
claim: Actual edge-link transport fixes each special edge's transverse label pair, and a stated repeated-label-type protection condition yields a restricted minimum-six realization theorem with more than two global transverse labels.
license: citation-only
triage: anchor
strata_touched: []
---

# Source map for CFMP Sections 101-105

The continuation is appended to the existing file
`docs/develop/theory/CFMP_GEOMETRIC_REALIZATION_TWO_RESERVOIRS.md`.
Its Sections 95-100 are retained as an exact byte prefix from source commit
`77ad1479da9bddb36303159ca876debd71cdc40f`. The original main and
mixed-matching theory files are unchanged. This is written research for
independent review, not a published paper or a priority certificate.

## Credited primary geometric inputs

Costantino, Frigerio, Martelli and Petronio, *Triangulations of 3-manifolds,
hyperbolic relative handlebodies, and Dehn filling*, arXiv:math/0402339,
Conjecture 0.8, is the external prescribed-triangulation target.
The present result retains the strictly hyperideal setting with every
boundary component closed of genus at least two. Torus-end completeness
is not addressed.

https://arxiv.org/pdf/math/0402339

Luo and Yang, *Volume and rigidity of hyperbolic polyhedral 3-manifolds*,
arXiv:1404.5365, Theorems 1.4 and 6.3 and the positive-length classification,
supply a maximum-volume angle structure realized by one shared positive
global generalized length vector. Flat tetrahedra remain possible in that
input theorem. Theorem 6.3 on printed page 21 was inspected as a PDF image
in this continuation. The existence statement is used as written; nearby
prose saying convex is not imported as a volume-convexity assumption.

https://arxiv.org/pdf/1404.5365

Frigerio and Moraschini, *On volumes of truncated tetrahedra with constrained
edge lengths*, arXiv:1801.05326, Section 1.1, formulas (1)-(5), supplies the
classical forward and inverse angle/length formulas. Printed page 6 was
successfully inspected as a PDF image. No lower-volume or edge-bound
hypothesis from a separate theorem is silently dropped.

https://arxiv.org/pdf/1801.05326

The new proof does not depend on Zhao or Ge version-specific claims.
Keyword searches produced many irrelevant results and are not presented
as a completed novelty investigation. The successful primary-source
checks support the actual inputs; they do not establish global priority.

## Existing repository inputs and new live step

The main volume Section 42.2 constructs a strict positive hyperideal angle
structure under the retained minimum-six and strict-boundary conditions.
Section 51.2 shows that any actual global label type appearing at least
three times must be genuine in a shared zero-curvature generalized metric:
a flat pi slot would otherwise transport to at least three pi contributions
on the same actual edge. These results are reused, not counted again.

The existing Section 96.1 proves the paired-length angular demand

`(r,a,b,o,a,b) genuine and r>=1+a+b => 2theta+beta+delta>pi`.

The new live combinatorial interface is Section 101.1. Partition actual
edge labels into H and S. In every tetrahedron require a vertex frame
`(R,A,B,O,A,B)`, with distinct A,B in H; R,O may repeat and may belong to
either set. A special edge e in S only occupies axial slots. Every face
containing it has the other two actual labels A,B. Face transport and the
connected normal circle therefore fix the same unordered pair P(e) over
its entire star. Different e can have different pairs. This fixes the
width around that star without making unrelated global lengths equal.

## Exact global realization hypotheses

Theorem 102.1 assumes the actual finite connected orientable face-paired
ideal triangulation and strict boundary setting, all degrees at least six,
and the paired frame condition above. Let Z be the set of tetrahedra whose
fully named label type, up to vertex permutation, occurs at least three
times. It additionally requires:

- Every h in H occurs in some Z tetrahedron.
- In every tetrahedron outside Z, each axial label that lies in H belongs
  to that tetrahedron's own transverse pair.

The first condition supplies genuine positive-angle witnesses for all H
labels and prevents their saturation. A remaining flat must use its axial
pair, and the second condition ensures a selected special edge dominates
the local width. A selected special label has exactly one flat appearance;
saturation would give degree two. The fixed pair transports the width
bound to all its at least five genuine appearances. A repeated dominant
special edge in one genuine block would itself force that block flat,
so these appearances have disjoint transverse slots. Section 96.1 then
requires more than 6pi on only two actual labels, whose total budget is
4pi. This excludes all flats without cross-block angle averaging.

The number of transverse labels, special labels, and tetrahedra is
unbounded. There is no role balance, global automorphism assumption or
equality between different H edge lengths. The protection and axial
compatibility hypotheses are substantive. This is not an unconditional
superset of every object in the earlier two-reservoir theorem.

Dropping axial compatibility leaves a precise necessary alternative:
any flat set must contain an unprotected flat whose axial H label lies
outside its own transverse pair. The proof does not exclude all such
exceptional blocks, arbitrary adjacent special slots or full CFMP.

## Fixed nonempty example and verification

Section 103 gives all 64 face pairings of a 32-tetrahedron example, with
actual degrees U,V,X,Y equal to six, A,C equal to 52, and B equal to 64.
The intersection of the actual label sets of all tetrahedra is only {B}.
Thus no two distinct actual global edges occur in every block, and the
earlier two-actual-reservoir theorem cannot simply be reapplied.

The transverse pairs are {A,B} and {B,C} in two regions. Tetrahedra 1 and
17 contain repeated opposite special labels U and X. Actual label-type
class sizes are 1,1,1,1,3,3,5,5,6,6; the four unprotected blocks are
0,1,16,17 and have purely special axial labels. The other 28 blocks
protect all three H labels. Three distinct global labels do not imply
that all three numerical lengths differ; no such numerical claim is made.

The first 62 face permutations are odd inside their respective halves;
the last two are even and connect opposite tetrahedron orientations.
The full edge circuits and fourteen independent link-vertex fan cycles
are checked. The single boundary link has (V,E,F)=(14,192,128), Euler
characteristic -50 and genus 26. The exact initial maximum corner sum
normalized by pi is 503/1248. The initial rational angles are not claimed
to be the final shared-length geometry.

Connected cyclic covers give 32n tetrahedra, 7n actual edges and manifold
Euler characteristic -25n. This uses metric lifting. The protection
certificate may change when labels split, and is not asserted to survive
unchanged in every cover. No new census/homeomorphism type is claimed.

The published standard-library checker is
`docs/develop/theory/cfmp_paired_transport_check.py`. Its exact executed
bytes have Git blob `8b2dc8b6cd374f8088ce9107134423230623d9fb`.
It validates the fixed face table, orientations, actual edge classes,
ordered first returns, independent link fans, named S4 label types,
protection conditions, pair transport, repeated special labels and exact
rational angles. A deliberately incorrect cross-face map is rejected.
The finite analytic cross-check uses 2500 genuine paired-length examples,
including 1622 obtuse target angles. Every sample satisfies the existing
Section 96.1 demand. The smallest sampled excess is approximately
0.2710652331 radians; it is not a uniform lower bound for the theorem.

Finite combinatorial checks and floating-point samples supplement the
written proofs. They are neither interval arithmetic nor Lean proofs.
No project CI, Lean build, Scribe projection, admission, Freeze or
independent mathematical-review approval accompanies this publication.
The original Scribe Statement and all Lean/formal-status sources remain
unchanged.
