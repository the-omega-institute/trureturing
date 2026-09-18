---
bibkey: zhao2026cfmpincidence
authors: Xinrong Zhao
year: 2026
title: Combinatorial Ricci Flows and Hyperbolic Structures on a Class of Compact 3-Manifolds with Boundary
doi: 10.48550/arXiv.2601.15174
url: https://arxiv.org/html/2601.15174v1
claim: The general valence-nine theorem and cube monotonicity are existing results; the accompanying theory proves explicitly restricted lower-valence incidence criteria without claiming the full CFMP conjecture.
strata_touched: []
license: citation-only
triage: anchor
---

# CFMP geometry and incidence-dependent length barriers

## Verified locators and primary-source scope

1. Francois Costantino, Roberto Frigerio, Bruno Martelli and Carlo Petronio,
   *Triangulations of 3-manifolds, hyperbolic relative handlebodies, and Dehn filling*,
   Commentarii Mathematici Helvetici 82 (2007), 903-934.
   https://arxiv.org/abs/math/0402339
   https://arxiv.org/pdf/math/0402339
   The retrieved v2 contains Conjecture 0.8: every ideal triangulation with
   edge valences at least six is realized by hyperbolic partially truncated
   tetrahedra. The prescribed triangulation, not just some triangulation of
   the same manifold, is the object to be realized. The text distinguishes
   already-proved hyperbolicity of the underlying manifold from this stronger
   realization claim. Equal-valence regular realizations are already known.

2. Ke Feng, Huabin Ge and Bobo Hua, *Combinatorial Ricci flows and the
   hyperbolization of a class of compact 3-manifolds*, Geometry & Topology
   26 (2022), 1349-1384, DOI 10.2140/gt.2022.26.1349.
   https://arxiv.org/abs/2009.03731
   https://arxiv.org/pdf/2009.03731
   Read the original abstract, Theorems 1.5, 1.6, 3.9 and the co-volume/flow
   arguments in Sections 4-5 in the retrieved PDF text. The general threshold
   is ten. Theorem 1.6 already gives convergence from every positive initial
   vector once a genuine zero-curvature metric exists. Theorem 3.9 gives a
   larger genuine-metric cube up to arccosh(3). Our smaller arccosh(2) cube is
   rechecked directly by the displayed cosine inequalities and is not claimed
   as a new discovery. The author order and spelling were checked on arXiv.

3. Xinrong Zhao, the present bibkey, arXiv:2601.15174v1, January 21, 2026.
   https://arxiv.org/html/2601.15174v1
   Read the full primary HTML, especially Theorems 1.1/1.5, 2.12,
   Lemmas 2.2 and 3.4, and the opposite-edge/adjacent-face estimates of
   Sections 4-6. The general threshold is nine. No peer-reviewed publication
   status is asserted here. Its cube monotonicity already controls the four
   adjacent variables. The accompanying theory proves that elementary
   derivative sign explicitly, rather than borrowing the degree-nine theorem
   for a triangulation containing degree-eight edges.

4. Feng Luo and Tian Yang, *Volume and rigidity of hyperbolic polyhedral
   3-manifolds*, arXiv:1404.5365v2.
   https://arxiv.org/abs/1404.5365
   The primary abstract was read. The tetrahedron length characterization,
   Schlaefli/co-volume formula and global rigidity are also explicitly stated
   with original locators in the two flow papers. We do not claim a complete
   independent audit of every proof in Luo-Yang.

5. Ke Feng, Huabin Ge and Yunpeng Meng, *Hyperbolization and geometric
   decomposition of a class of 3-manifolds*, arXiv:2503.07421v1.
   https://arxiv.org/abs/2503.07421
   https://arxiv.org/html/2503.07421v1
   Its mixed-boundary result requires proper gluing, ideal-edge valence at
   least six and hyper-ideal-edge valence at least eleven. It does not prove
   the pure hyper-ideal valence-eight cases considered here. The primary
   abstract and relevant HTML theorem statements were checked.

PDF screenshots of the CFMP and Feng-Ge-Hua pages were attempted and returned
cache-miss/internal errors. The parsed primary texts and Zhao's full HTML
were available. No successful visual inspection of those PDF pages or an
unparsed figure/table is asserted. Figure geometry is not used as evidence
for any new inequality.

## Exact mathematical delta

The new owner is `docs/develop/theory/CFMP_GEOMETRIC_REALIZATION.md`.
It fixes actual global edge variables and counts local occurrences, allowing
self-identifications. For caps b_e in (1,2], the local dihedral cosine bound
uses the actual four adjacent cap values and the opposite lower endpoint one.
If the resulting angular sum on every upper face is strictly greater than
2pi, a uniformly positive lower face can be chosen. The full length box is
proved to lie in the nondegenerate geometric domain. A genuine co-volume
minimum in that box is forced into its interior, producing a zero-curvature
metric of the prescribed triangulation. This proof does not assume existence
as an input or treat an arbitrary degenerate limiting vector as a geometry.

The first explicit application allows degree-eight edges and degrees at
least twelve. Caps are 2 and 8/5 in cosh-length. An eight-edge occurrence
with at least three high adjacent edges has squared cosine at most 833/1677,
strictly below 1/2. A high edge has cosine at most 37/43, strictly below
sqrt(3)/2. Thus all required angular sums are strictly inward.
A second application lets six of the eight occurrences have four high
neighbors and leaves the other two unrestricted. Its exact triple-angle
certificate uses cos(3 acos(103/153))=-2862473/3581577 < -7/9.
These conditions are sufficient, not equivalent to min valence eight.
The proof method is classical convex-variational geometry plus the displayed
incidence-dependent estimate. No mathematical first-discovery claim is made
without a further priority review.

## Relation to the contextual spacetime model

Read `CONTEXTUAL_SPACETIME_ARITHMETIC_ML.md`, especially Sections 2-4, at dev
9740a07f66b6f1fe7b9fe634c88c1c9d115e22ff. Its common-world condition requires
repeated references to the same variable to use one shared value; joint
responses are not automatically a Cartesian product of local responses.
Here that means one length per global edge, correct opposite/adjacent roles,
and incidence sums with multiplicity. Independent box corners are only
conservative bounds, not falsely asserted actual global states.
This methodological connection supplies no automatic curvature estimate,
physical spacetime identification or proof of geometric realization.

## Search and delivery boundary

September 16, 2026: searched primary arXiv sources and the combinations
hyper-ideal, valence eight, CFMP and geometric realization. Bounded searches
found the general ten and nine results, but no proof or counterexample for
all-eight or all-six triangulations. Some search results were secondary
machine-generated summaries; those were not used as mathematical sources.
Repository searches for CFMP and hyper-ideal returned no existing owner,
so the new theory volume is a distinct geometric domain rather than a copy
of the surface-congruence volume. This is not an exhaustive novelty search.

Read the current information-escape specification and relevant CLAUDE
admission text. Also inspected other-contributor PR results, including
loning's #7820 theory continuation, alongside the actual spacetime source.
No assertion of having mathematically reviewed every current PR is made.

The theory volume contains ordinary proofs and source provenance. The
unrestricted degree-eight target and original CFMP conjecture remain open.
The restricted theorem has no numerical hypothesis left unproved; its
additional hypotheses are the explicit incidence rules.

## Second increment: exact identification constraints and nonvacuous families

Sections 5-9 were appended without changing Sections 1-4.

Section 5 retains the actual equality of a local edge with its opposite when
both represent the same global edge. The upper-face calculation must then
use the SAME cap for both, not independently set the opposite one to its
lower endpoint. With caps two for degrees eight/nine and 19/10 for degrees
at least ten, realization follows if each degree-eight edge has at least six
opposite-identified occurrences, and each degree-nine edge has at least two.
The strict angular sums are certified by exact triple/seven-angle polynomial
identities. This equality constraint need not survive passage to a covering
triangulation, so no such cover-stability claim is made.

Section 6 allows every edge degree at least six, provided each occurrence
of an edge below degree twenty has four adjacent edges of degree at least
twenty. Caps two and 61/50 give exact cosine bounds 2471/4971<1/2 and
389/411<cos(pi/10), respectively. There is no bound on the dimension of the
length space or the tetrahedron count. The length space dimension is the
actual number of GLOBAL edges, and the manifolds are three-dimensional.

Section 7 gives two fully specified actual face-pairings, with odd gluing
permutations, no reversal of an edge, and closed orientable vertex links:
four tetrahedra with edge degrees (8,16) and one genus-three boundary; six
tetrahedra with edge degrees (6,6,24) and one genus-four boundary. Their local
color conditions are verified. Taking cyclic covers produces unbounded,
pairwise nonhomeomorphic families by Euler characteristic. This is a proof
of nonvacuity and unbounded scope, not a claim that the four-tetrahedron
example was previously unknown: CFMP itself reports experimental checks of
all triangulations with at most four tetrahedra. The equal-valence regular
construction is also old and explicitly credited.

Section 8 proves a limitation of the independent-opposite-endpoint cap test.
At a global minimum cap b, every local cosine lower bound is at least
f(b)=(2b^3+b^2+1)/(2b^3+3b^2-1)>=7/9. Therefore the Section 3 certificate
cannot succeed on ANY all-eight or all-nine triangulation, even with
nonuniform caps in (1,2]. Such constant-valence triangulations are nevertheless
geometric by the classical regular-tetrahedron construction. This is a
counterexample to a proposed proof mechanism, not to CFMP or to all possible
coupled barriers. It justifies keeping true equalities and seeking additional
joint constraints instead of tuning the same incomplete cap scheme.

Section 9 uses the exact remaining variational obligation. In a minimum-eight
triangulation the assignment 2pi/d(e) is a strict angle structure. Luo-Yang
Theorems 1.4 and 6.3 already give a unique maximum-volume angle structure and
a positive GENERALIZED length realization. Its only nongeometric tetrahedra
have angles (0,0,0,0,pi,pi), with the pi angles opposite. The full original
PDF was now retrieved and the theorem/Section 6.3 text inspected. A screenshot
of PDF page index one (printed page two, including Theorem 1.4) succeeded.
No claim of independently rechecking the entire paper is made. Excluding
these flat tetrahedra in the maximum is the missing full-eight existence
step; positive angle feasibility or energy monotonicity does not exclude them.

## Exact checks actually executed, outside the repository delta

The local verification script checks the derivative numerator identity,
seven displayed cosine evaluations, the squared three-high bound, all exact
triple/seven-angle inequalities, and the rational no-go factorization.
Numerical radian margins are display-only; the strict signs have rational
polynomial certificates. A two-variable floating-point root was also explored
for the four-tetrahedron example; its success is not used as an existence
proof or certified geometric root.

Three face-pairing packets were checked. Two are the stated (8,16) and
(6,6,24) examples. The third is a second (8,16) packet with an opposite-pair
low edge, checking the Section 5 condition. The initial searches used exact
union-find bookkeeping. A separate graph-component implementation, with no
use of the searcher's output classes, rechecked complete face pairing,
orientation parity, connectedness, oriented-edge reversal, circular normal
links, vertex-link Euler characteristics and all incidence hypotheses. Both
implementations are local diagnostics authored in this session; they are not
independent human reviews, a Regina/SnapPy certificate or Lean certification.

No tests of finitely many pairings establish the unrestricted conjecture.
The mathematical theorems quantify over all actual triangulations satisfying
the displayed incidence rules and use the complete analytical proof. Their
priority has not been established by an exhaustive literature review.

## Third increment: nineteen is sharp for the specified two-cap scheme

Section 10 strengthens the isolated-low-edge result from threshold twenty to
nineteen, with exact caps 2 and 153/125. The low cosine is
31193/62443<1/2. The high cosine is 243/257<cos(2pi/19); the proof uses
pi<22/7 and a sixth-order Taylor lower bound at 44/133, whose rational
margin is 15920790096478/64011128373838485. It has no unproved numerical
sign assumption. The previous six-tetrahedron example and all its cyclic
covers satisfy the strengthened rule.

The same section proves nineteen is the smallest threshold attainable by
that SPECIFIED uniform two-cap, independent-opposite-endpoint, per-occurrence
scheme. The scheme permits both low cap b and high cap c to vary in (1,2],
with c<=b. The low requirement forces c^2<3(b-1)/2. Differentiating
(sqrt(3(b-1)/2)-1)/b^2 proves its maximum occurs at b=2, so the best high
cosine is still greater than 47/50>cos(pi/9). Thus threshold eighteen or
smaller cannot satisfy the two simultaneous inequalities. This is a limitation
of that estimate, not a nonrealizability claim at degree eighteen and not
an exclusion of more detailed incidence, positive lower, or nonrectangular
barriers.

The final diagnostic run also verifies the two new cosine values, the exact
Taylor margin, the derivative identity for the two-cap extremum, and the
positive-integral formula for 22/7-pi. The graph checker rechecks the new
nineteen-neighbor criterion on the same actual packets. No new mathematical
independence or kernel certification is inferred from using a second program.
