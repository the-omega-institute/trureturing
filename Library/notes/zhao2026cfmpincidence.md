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

The active runtime has no Lean/lake or .NET executable. The current delivery
contains ordinary proofs and source provenance, not new Lean declarations,
Scribe compilation, a frozen theorem, an independent referee report, or a
CI result. No binding-only formal wrapper is added for an existing flow
result. The unrestricted degree-eight target and original CFMP conjecture
remain open in this work. The restricted theorem has no numerical hypothesis
left unproved; its additional hypotheses are the explicit incidence rules.
