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

## Triangle-seed continuation: Sections 106-110

The same theory file now proves a strict extension of Theorem 102.1.
The new certificate permits an axial H label outside the block's own
transverse pair, when a genuine opposite-pair triple supplies the relevant
shared-length inequality. All original strict-boundary, actual-manifold,
minimum-six and paired-frame hypotheses remain attached.

### All-special-edge bound and genuine seeds

Assume each h in H has a genuine occurrence. Section 106.1 proves for
EVERY special edge e, with transported pair {A_e,B_e},

`x_e < 1+x_Ae+x_Be`, where `x_e=cosh(ell_e)`.

It covers both m_e=0 and m_e=1 flat pi occurrences. A hypothetical dominant
special length cannot repeat axially in a genuine block, because the exact
paired flat threshold would fail. Its disjoint genuine transverse slots
then require more than `2*(d(e)+m_e-4)*pi >= 4pi` by existing Section 96.1,
while the two actual transverse labels have total budget 4pi. The m_e=0,
d(e)=6 boundary case remains a strict contradiction.

The stronger conclusion localizes EVERY residual flat: it has a foreign
axial H label h with `x_h >= 1+x_A+x_B`. If the other axis is special the
inequality is strict. This cannot coexist with a genuine opposite-pair
block `(h,A,B,h,A,B)`, which forces the opposite strict inequality.

Two distinct copies of one named three-label opposite-pair type are
genuine by the existing saturation argument: if flat, each would contribute
two pi to the same actual label. Each genuine triple {i,j,k} gives
`x_i<1+x_j+x_k` and its two cyclic versions. These statements concern
cosh coordinates; they are not ordinary edge-length triangle inequalities.
The saturation rule and cosine factor are credited existing inputs.

### Exact larger realization certificate

Let Z retain its three-copy definition. Let D consist of blocks in at least
two copies of a three-distinct-label opposite-pair type, and put K=Z union D.
Let Q be the triples realized by three-label opposite-pair blocks in K.
Every H label must occur in K. For each block outside K, an axial H label
must either belong to its own transverse pair or form a triple in Q with
that pair. These are finite combinatorial conditions on actual names.

Theorem 108.1 proves geometric realization of the same prescribed
triangulation, with no role balance or cross-block angle averaging.
Theorem 106.1 bounds special axes; seed triples bound foreign H axes;
axes already in the pair satisfy the bound by positivity. The two axial
bounds contradict the exact flat product threshold. Transverse flats
would saturate an H label already witnessed in K.

Every old Theorem 102.1 certificate satisfies the new certificate because
Z is contained in K. In the particularly simple case H={A,B,C}, two
opposite-pair ABC blocks suffice; no additional axial-membership condition
is then needed on the other paired blocks. Neither the paired-frame nor
the seed-coverage assumptions have been removed in general.

### Fixed example strictly outside the old certificate class

The full fourteen-tetrahedron, twenty-eight-face-pair table in Section 109
has actual degrees U,V,A,B,C equal to 6,6,22,33,17. Its one boundary link
has (V,E,F)=(10,84,56), Euler characteristic -18 and genus ten.
Mixed-parity face maps are checked against an explicit tetrahedron-sign
assignment; all ten link-vertex fans and ordered first returns are checked.
The exact maximum normalized initial corner sum is 287/561.

Named type multiplicities are 1,1,2,5,5. Blocks 0,1 are the two ABC seeds;
blocks 2 and 8 are unprotected foreign-axis blocks, with transverse pairs
{A,B} and {B,C} respectively. The same seed triple resolves both. Every
possible old paired frame forces A,B,C into H, but either seed block has
only two copies and has a foreign H axis in every frame. Thus no old
Theorem 102.1 certificate exists, even after changing H and the frames.
Only B occurs in every block, excluding the literal two-common-edge
hypothesis of Theorem 97.1 as well. This does not claim failure of every
other possible proof or a new census/homeomorphism type.

Connected cyclic covers lift the established metric to 14n tetrahedra,
5n actual edges and manifold Euler characteristic -9n. The same-name seed
condition is not asserted to survive label splitting under a cover.

### Sources and validation boundary

The primary geometric inputs remain Frigerio-Moraschini arXiv:1801.05326,
Section 1.1 formulas (1)-(5), and Luo-Yang arXiv:1404.5365, Theorem 6.3.
Printed pages 6 and 21 respectively were successfully inspected as PDF
images for this continuation. The proof does not use Zhao or Ge
version-dependent claims. Keyword search was insufficient to establish
worldwide priority, which is not claimed.

The supplementary standard-library `cfmp_triangle_seed_check.py` checks
the fixed actual topology, seed and protection predicates, pair transport,
exact rational initial angles, all old H/frame alternatives and rejection
of a deliberately broken face map. It also checks 1000 exact rational seed
factor identities, 2500 dominated genuine paired-length samples (1853
obtuse targets) and 188 integer resource cases. The sampled minimum excess
0.2396092815 radians is not a uniform theorem bound. Finite/floating checks
supplement the continuous and unbounded written proofs.

This is ordinary written research pending independent review. No new Lean,
project CI, Scribe compilation/projection, admission or Freeze accompanies
it. Full CFMP, arbitrary unframed or unprotected incidence, and torus-end
completeness remain outside the established conclusions.

## Intrinsic witnesses and degree-four closure: Sections 111-118

This increment preserves the concurrent Sections 106-110 and appends to
the same theory owner. Written proofs were published in source commit
`a4b4024fc351995be22ad02270a7529953445aa2`, after the supplementary checker
commit `814c8a296da5656ef1f3c5822f47561b56350d77`. The previous theory prefix
is unchanged: GitHub compare reports 336 additions and zero deletions.
No new Lean theorem or independent mathematical-review approval is claimed.

### Intrinsic genuine-occurrence witnesses

In the general paired frame of Section 101, transverse flat selection A,A
forces a>b and a-b>=sqrt((r+1)(o+1)); the opposite selection forces b>a.
These follow from the raw cosine identities, including their signs in the
flat domain. They are not inferred by using genuine inverse-angle formulas
outside their domains.

If a special edge e has no genuine appearance, it has exactly two pi
appearances. Every zero appearance must select the same larger transverse
label. One such block consumes that label's entire 2pi budget, so at most
one block supplies zeros; that block contains at most two e slots. Hence

`d(e)<=4`.

At degree at least six, e and both labels in its transported pair P(e)
have genuine appearances without requiring any repeated-type seed.
Section 112.1 therefore removes the all-H-genuine premise from the
concurrent Section 106.1 length bound:

`cosh(ell_e)<1+cosh(ell_Ae)+cosh(ell_Be)`.

The angular budget calculation is explicitly reused from that existing
bound. The new input is the automatic genuine-occurrence witness, not a
second claim of discovery for the same capacity algebra.

Given known genuine labels N, two copies of a fully named tetrahedron type
are genuine if each possible opposite pi pair contains a label in N.
Finite closure starts with S, its transverse pairs and old triple-copy
blocks. Theorem 113.2 realizes the paired triangulation when the closure
covers H and the remaining unprotected blocks have compatible axial H
labels. It retains that last condition; arbitrary foreign axes are not
silently included.

The full 22-block example has degrees (6,6,6,6,29,52,27), a genus-16
boundary link (14,132,88), and maximum initial normalized corner 313/702.
Its named type multiplicities are ten singletons and six doubletons.
There are no triple-copy types and no duplicated three-label diagonal
seed types. The former protection cores are empty, while intrinsic
witnesses and the two-copy rule suffice. Only B occurs in every block.
The four special stars use {A,B} or {B,C}; repeated axial labels are real.

### Coupling the two stars closes the degree-four two-reservoir case

Theorem 116.2 assumes exactly two designated actual transverse labels A,B,
every block framed as (R,A,B,O,A,B), and all other labels special with
`d(e)>=4`. The actual orientable finite ideal manifold and genus-at-least-
two boundary hypotheses remain. Special labels and blocks are unbounded
in number; role balance, equality of A and B lengths, global symmetry and
repeated-type seeds are not assumed.

The strict initial angle structure is constructed directly at degree four.
Actual link counting gives t>|E|>=3 and d(A),d(B)>=2t. For t>=5 the usual
2pi/d assignment is strictly feasible. At t=4 the only potential equality
would force the three degrees to be 4,8,8, contradicting total degree 24.
Thus the Luo-Yang maximizer theorem is used with its actual premise;
the minimum-six strict-angle theorem is not applied out of range.

At degree four, an entirely flat special star would have one zero-block
with two copies of the special axis. If its transverse selection is A,A,
then a-b>=r+1 and A is saturated. A pi-block for that special edge forces
its opposite o>1+a+b, so the opposite is another special label. All its
appearances must also be flat because they contain saturated A; its own
zero-block would demand a-b>=o+1. This is impossible. Section 115.1 thus
provides genuine witnesses for every label in the two-reservoir class.

A hypothetical flat axial pair satisfies (r-1)(o-1)>=(a+b)^2. Choose a
special side r>=1+a+b. Its g>=3 genuine target angles sum to pi and its
appearances lie in distinct blocks. Existing Section 96 positive remainders
at an angle <=pi/3 imply lambda_r^2>1/3. The same flat product gives

`lambda_o^2 >= K/(1+2(r-1)/(a+b)^2) > 1/7`,

where K=(sqrt(a^2-1)+sqrt(b^2-1))^2/(a+b)^2. The denominator is below 7/3
by the same genuine r witness. This is a bound transferred across the flat
pair, not an assumed lower bound for the other side.

Scalar convexity gives more than 3pi of distinct transverse-slot demand
from the r star. If the other flat label is A or B, the true transverse
budget is at most 3pi, a contradiction. If it is a different special,
its response lower bound gives more than pi even after allowing two axial
appearances per genuine block. The two genuine block sets are disjoint:
a block containing both axes would reproduce the original flat length
vector. Their disjoint demands therefore exceed 3pi+pi=4pi, contradicting
the total A,B budget. This completes the restricted degree-four theorem.

The old Section 100 g=3 local-star check remains valid. Its uncompleted
opposite star was the missing global information. The present argument
uses that other star and proves disjointness before adding their costs.
It does not prove unrestricted minimum-four or full CFMP.

The full 8-block example has degrees (4,4,4,20,16), one genus-four boundary
link (10,48,32), and maximum initial normalized corner 29/40. Four extra
A axes and no extra B axes give ell_A<ell_B by actual positive angular
mass and the credited Section 95.5 angle-order identity. Degree inequality
alone is not used to infer length order. Neither example's census or
homeomorphism-type novelty is claimed. Metric lifting gives the respective
cyclic-cover families with Euler characteristics -15n and -3n; their
split labels need not satisfy the same named combinatorial certificate.

### Formalization and executed-check interfaces

The four-degree chain is raw cosine identities -> Section 111.2 all-flat
count -> Section 115.1 nonsaturation -> Section 116.1 partner response ->
Section 116.2 disjoint-star budget. It does not use the six-degree length
bound in Section 112.1. The minimum-six chain uses Sections 111,112,113.
These degree guards and the factor-of-two correction for repeated partner
appearances are explicit interfaces for parallel formalization.

The published standard-library checker is
`docs/develop/theory/cfmp_intrinsic_protection_check.py`. Its executed bytes
have Git blob `bd5f5be27f1fbfe3a66b24e498826dc43d7c9b2a`, matching the remote
source. Both complete fixed tables were checked for every face slot,
actual label class, ordered first return, independent link-vertex fan,
named type, transported pair and exact rational initial angle. A bad
face map preserving the omitted-vertex condition is correctly rejected.
Analytic checks include 6000 raw identity samples, 1541 A-transverse and
1412 B-transverse flat samples, 3000 genuine dominated inputs, 188 exact
count cases and 3000 partner-transfer cases. The maximum relative raw
identity discrepancy was 1.346171152143567e-15. Sampled lower margins
are not promoted to universal constants or interval certificates.

This increment inspected Luo-Yang printed pages 2 and 21 as images.
Frigerio-Moraschini parsed text was read, but its page-6 image request
failed; no successful image check of that page is claimed for this run.
The preceding historical image records are preserved, not reassigned.
Broad literature searches were insufficient for global novelty claims.
Classical formulas, the positive-length dichotomy and the maximizer are
credited inputs. No Zhao or Ge version-specific theorem is needed.

All existing Lean, Scribe and formal-status files are unchanged by this
increment. No project CI, Lean build, Scribe projection, admission or
Freeze was executed. Written proofs remain pending independent review.
General unpaired incidence, unrestricted foreign axial labels and torus-end
completeness remain outside the established scope.
