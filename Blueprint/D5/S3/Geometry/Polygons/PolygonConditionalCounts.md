# Actual original chord sets

## Abstract

Catalan counts of complete conditioned polygon fibres

V(n) means ZMod(n); H(n,P) is the subtype of every finite original chord set T satisfying Carrier.IsTriangulation T and P subset EarCenters(T). Triangulation includes internal-diagonal validity, pairwise noncrossing and full maximality. Compatible(P) means that distinct ears with centres in P do not cross. ConditionFiber is the existing complete original-carrier subtype, including its trace constraint; with both trace arguments empty that constraint is automatic. No completion is selected or quotient taken.

**Theorem 1.1 (All completions containing compatible forced ears).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies (\operatorname{Compatible}\left(P\right) \implies (\operatorname{Natcard}\left(\operatorname{H}\left(n, P\right)\right) = \operatorname{catalan}\left(((n - \operatorname{card}\left(P\right)) - 2)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonConditionalCounts.forced_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The actual iterated deletion equivalence forcedEquiv identifies H(n,P) with every triangulation of the (n-card(P))-gon. The licensed supplier encard_setOf_isTriangulation is applied through the identity on whole chord sets; both carrier inverses are reflexive equalities. Its catalanNumber is definitionally the receiver's Mathlib catalan. This is the containing-event count in B-32, formula (32.1).

**Definition 1.2 (Integer alternating Catalan sum).**

$$\forall n \in Nat,\; \forall p \in Nat,\; \forall q \in Nat,\; (\operatorname{Npq}\left(n, p, q\right) = \sum _{j\in \operatorname{range}\left((q + 1)\right)} ((((0 - 1)^{j} \cdot (\operatorname{choose}\left(q, j\right): \mathbb{Z})) \cdot (\operatorname{catalan}\left((((n - p) - j) - 2)\right): \mathbb{Z}))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonConditionalCounts.Npq` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Npq has values in the integers. All subtractions inside the Catalan index are natural subtraction; choose and catalan are cast to the integers before multiplication. This total definition does not assert any geometric existence or positivity.

**Theorem 1.3 (Every completion with forced P and forbidden Q).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies (\operatorname{Disjoint}\left(P, Q\right) \implies (\operatorname{Compatible}\left(\operatorname{union}\left(P, Q\right)\right) \implies ((\operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, \operatorname{empty}\left(\right), \operatorname{empty}\left(\right)\right)\right): \mathbb{Z}) = \operatorname{Npq}\left(n, \operatorname{card}\left(P\right), \operatorname{card}\left(Q\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonConditionalCounts.conditional_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary disjoint P,Q with compatible union, Mathlib Finset.inclusion_exclusion_card_inf_compl counts the complement of the forbidden-ear events inside the complete forced-P carrier. Every event intersection is equivalent to the complete forced-(P union S) carrier, S subset Q. The term is Catalan(n-card(P)-card(S)-2). Mathlib Finset.sum_powerset_apply_card groups these terms by card(S), giving the binomial coefficient. This proves the cardinality part of (37.3), without its positivity assertion.

The source is AURIC_FIB_ATOM_INTRINSIC_CLASSIFICATION_AND_POLYGON_GEOMETRY, B-32 and B-37.2, at revision 4b62d1ff02a702a51332eae3324db7daac400cd5. Its four parameter cases (p,q)=(2,2),(3,3),(2,4),(4,2) are instances of the same theorem at every permitted cyclic placement. Interchanging P,Q is another application with disjointness reversed and union commuted; it uses Nqp, without identifying the weights.

The compatible-card bound gives 2 card(P union Q) <= n. For each j <= card(Q), disjointness gives card(P)+j <= floor(n/2), so n-card(P)-j >= ceil(n/2) >= 7. Thus the displayed Catalan indices are legal ordinary indices; natural truncation in the total definition is inactive on the source domain.

Formula (37.6) follows from this same theorem applied to P union I and Q when I subset E_K(P union Q) and Compatible(I). Membership in E_K supplies disjointness from P union Q and compatibility with every one of its ears. Together with the two internal compatibility assumptions, these facts give compatibility of P union I union Q; card(P union I)=card(P)+card(I). Its ConditionFiber is exactly the original complete carrier with P and I forced and Q forbidden. Every nonzero term has the same legal-index bound using this larger union.

Positivity of Npq, the general exact-trace formula (37.7), strict flip inequalities, normalized inequality (37.4), and its equality classification require their own arguments. Catalan enumeration and finite inclusion-exclusion supply the counts below.

For the twenty-gon take U=ZMod(20), and let C20 have adjacency y=x+1 or x=y+1. Let D be any six-element subset of a single parity class, P any two-element subset of D, and J any cyclically independent subset of U outside D and every neighbour of P. Set A=D minus P and R=A union J. J may be empty, nonmaximal or in the same parity class as D. Count O using every original maximal noncrossing internal chord set T with EarCenters(T) intersect D=P and EarCenters(T) disjoint J. There is no restriction on its other ears, no selected completion, and no change of polygon. This is the count and graph correspondence underlying B44.2, formula (44.3), of AURIC_FIB_ATOM_POLYGON_TWENTY_GON_SAME_PARITY_DEFICIT.

This condition on the same T is equivalent to forcing P and forbidding R. In the finite carrier of all triangulations forcing P, use the ear-membership event at each vertex of R. Finset.inclusion_exclusion_card_inf_compl gives the sum over every I subset R with sign (-1)^card(I). The original event-intersection equivalence preserves the entire chord set T and identifies its carrier with all triangulations forcing P union I. P is disjoint from R and has no adjacency to R. Hence P union I is independent exactly when I is independent in C20. If I is not independent, PolygonCompressionTrace.earCenters_independent makes this forcing carrier empty, so its term is zero. No containing-event Catalan formula is applied to such a union.

For independent I, PolygonCompressionTrace.independent_iff_noncrossing gives compatibility of P union I. Apply forced_card at n=20 to this union. Its size is 2+card(I), so the count is Catalan(16-card(I)); the sign still uses card(I). Filtering away the empty forcing carriers gives O, cast to the integers, equal to PathCatalanFunctional.phi(C20,R,16). No binomial coefficient replaces the actual independent-subset multiplicities. At I empty the term is Catalan(16). Compatibility bounds card(I) by eight in every nonzero term, giving a reduced polygon of at least ten vertices and a Catalan index of at least eight.

The original graph G is C20 induced on the subtype of all x in R. Map each finite subset of this subtype to its image under subtype.val; the inverse takes the subtype of a subset of R. These maps preserve cardinality and independence, so phi(C20,R,16)=phi(G,univ,16). They preserve every vertex identity and every isolate, including the empty independent configuration. A and J give disjoint covering independent parts of this actual graph; the A part has four vertices and the J part has card(J) vertices.

Choose p in P. For x in R, the representative (x-p).val is nonzero. Sending x to that natural number is injective and takes every actual edge to consecutive natural numbers: the only possible wrap would pass through the excluded p. Thus G maps injectively to the natural-number Hasse path and is acyclic by SimpleGraph.IsAcyclic.comap. Its image may be disconnected and need not be an interval. Every neighbour of x still has original label x-1 or x+1, so every actual vertex has degree at most two.

P union J is independent and has size 2+card(J), so compatible_card_bound first gives card(J)<=8. Equality would make it a half-density independent subset of C20. To see the rigidity, translate P union J by one. The two disjoint sets have ten vertices each and therefore cover U, so membership alternates at each step. This gives a period-two membership predicate on natural representatives; Function.Periodic.map_mod_nat reduces it to the remainder modulo two. Applying it with a vertex of P puts every vertex of D into P union J. Since J avoids D this gives D subset P, contradicting their sizes six and two. Therefore card(J)<=7 without a maximality assumption. The actual graph has 4+card(J)<=11 vertices, and even the formal indices of the zero terms satisfy 16-card(I)>=5 for I subset R.

To compare this count with a graph having parts (4,7), let r=7-card(J) and form Hq by adjoining q new abstract isolates to G for 0<=q<=r, placing the new isolates in the J part. These are graph vertices, not added polygon vertices. The required padding comparison is Phi_16(G)>=Phi_16(Hr). An isolate-splitting and telescoping approach to this comparison requires Phi_15(Hq)>=0 for every q<r; those values concern the actual disconnected forests with their added isolates. The path-only theorem path_phi_nonnegative does not supply this for disconnected forests.

A further independent bound Phi_16(Hr)>=29205 is required at the fixed actual covering parts (4,7). A proposed structural route is Phi_16(Hr)>=Phi_16(P9 disjoint_union 2K1), followed by evaluation of the right-hand side. The comparison must respect the fixed parts and the actual isolates. The count identity alone establishes neither the forest nonnegativity needed for isolate padding nor this extremal bound. The original same-family deficit bound 69320276, the actual C0 case and the native operation, readout, continuation and resource correspondences remain separate questions.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionalCounts.Npq`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionalCounts.conditional_card`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionalCounts.forced_card`
- Dependency: [D5/S3/Geometry/Polygons/PolygonCatalanSupplier](PolygonCatalanSupplier.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarContraction](PolygonEarContraction.md)
