# Removing one observed ear by an actual diagonal flip

## Abstract

Injective flips between complete conditioned polygon trace fibres

**Theorem 1.1 (The conditioned flip is injective).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], ((14 \leq n) \implies (\forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall h \in \operatorname{ZMod}\left(n\right),\; ((\forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in ((P \cup Q) \cup H)) \implies (\forall j \in \operatorname{ZMod}\left(n\right),\; ((j \in ((P \cup Q) \cup H)) \implies \neg\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(j\right)\right))))) \implies (\operatorname{Disjoint}\left(H, (P \cup Q)\right) \implies ((h \in H) \implies ((R \subseteq \operatorname{erase}\left(H, h\right)) \implies \operatorname{Injective}\left(\operatorname{Flip}\left(P, Q, H, R, h\right)\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonTraceFlip.actual_flip_trace_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Vertices are ZMod(n), chords are Sym2(ZMod(n)), and ear(i) is the unordered chord with endpoints i-1 and i+1. IsTriangulation means that every chord is an internal diagonal, no two chords cross in cyclic order, and every missing internal diagonal crosses a present chord. EarCenters(T) consists of all i whose ear(i) belongs to T.

ConditionFiber(P,Q,H,R) is the subtype of all such finite chord sets T with P contained in EarCenters(T), Q disjoint from EarCenters(T), and EarCenters(T) intersect H equal to R. It includes every actual completion, including empty fibres. In the displayed statement n is arbitrary with n at least 14 and NeZero(n); P,Q,H,R are arbitrary finite vertex sets. Every pair of ears centred in P union Q union H is noncrossing, H is disjoint from P union Q, h belongs to H, and R is contained in H with h erased.

Write gamma=ear(h). For T in the fibre with trace insert(h,R), gamma belongs to T. The exact supplier IsTriangulation.existsUnique_isFlipReplacement selects delta, an internal diagonal absent from T, for which U=insert(delta,erase(T,gamma)) is an actual triangulation. The displayed Flip is actual_flip_trace_map with the hypotheses just stated; it sends the entire chord set T to U and retains the conditioned-fibre proof.

Maximality of T supplies a chord crossing delta. Noncrossing in U forces that chord to be gamma, so delta crosses gamma. Since all designated ears are mutually noncrossing, delta cannot be the ear at any centre in P union Q union H. The original parent PolygonConditionedFan.ear_injective distinguishes the erased ear from every other designated ear. Consequently every forced ear in P survives, no forbidden ear in Q appears, and the observed trace becomes exactly R.

For reconstruction, suppose two inputs produce the same U. Each replacement delta is the unique chord of U crossing gamma: every retained chord was in an input containing gamma and therefore cannot cross it. Thus the two replacement diagonals agree. Erasing this common delta gives equal copies of T with gamma erased; reinserting gamma recovers equal entire input chord sets. This proves injectivity across inputs, beyond the supplier's uniqueness of a replacement for a fixed input.

The consumed cardinality consequence actual_flip_trace_card_le follows by Fintype.card_le_of_injective. It compares the complete trace fibres with insert(h,R) and R, and supplies the one-ear step in PolygonStrictNormalization.actual_weight_antitone. The injective map also supplies the map whose missing image point yields actual_singleton_strict in that owner.

The original parent PolygonConditionalCounts.allEquiv identifies the two triangulation predicates by the identity on entire chord sets in both directions. The 69 declarations of PolygonCatalanSupplier are the sole shared source; this owner contains exactly the 32 additional licensed flip declarations with their original ClusterAlgebras names and proof bodies. Their source revision, spans, authors and Apache-2.0 license are specified in docs/reports/licenses/cluster-algebras-polygon-third-party.md. The conditioned trace construction and reconstruction are repository derivations; the diagonal-flip supplier is licensed reuse.

The result asserts injectivity, not surjectivity. It does not assume positivity of any fibre or restrict to selected completions. Strictness requires an actual conditioned triangulation outside the image, supplied separately by the two-crossing fan construction.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonTraceFlip.actual_flip_trace_injective`
- Dependency: [D5/S3/Geometry/Polygons/PolygonCatalanSupplier](PolygonCatalanSupplier.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonConditionalCounts](PolygonConditionalCounts.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonConditionedFan](PolygonConditionedFan.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarSlide](PolygonEarSlide.md)
