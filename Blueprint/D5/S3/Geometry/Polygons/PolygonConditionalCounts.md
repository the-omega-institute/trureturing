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

Formula (37.6) follows from this same theorem applied to P union I and Q when I subset E_K(P union Q) and Compatible(I). Membership in E_K supplies disjointness from P union Q and compatibility with every one of its ears. Together with the two internal compatibility assumptions, these facts give compatibility of P union I union Q; card(P union I)=card(P)+card(I). Its ConditionFiber is exactly the original complete carrier with P and I forced and Q forbidden. No new named specialization is retained. Every nonzero term has the same legal-index bound using this larger union.

This delivery does not prove Npq>0, exact-trace formula (37.7), strict flip inequalities, normalized inequality (37.4), or its equality classification. It does not assert a complete formalization of B-37.2. The general structural contraction is the new mathematical construction; Catalan enumeration and generic inclusion-exclusion are reused.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionalCounts.Npq`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionalCounts.conditional_card`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionalCounts.forced_card`
- Dependency: [D5/S3/Geometry/Polygons/PolygonCatalanSupplier](PolygonCatalanSupplier.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarContraction](PolygonEarContraction.md)
