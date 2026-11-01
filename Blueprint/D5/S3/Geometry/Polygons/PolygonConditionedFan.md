# Original cyclic vertices and internal diagonals

## Abstract

Literal forced-ear fans and original conditioned polygon completions

**Definition 1.1 (Cyclic independence).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Independent}\left(P\right) \iff (\forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in P) \implies \neg (((i + 1) \in P)))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonConditionedFan.Independent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Independence forbids consecutive centres in ZMod n, including across the cyclic seam.

**Definition 1.2 (Literal forced-ear fan).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall h \in \operatorname{ZMod}\left(n\right),\; \forall e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in \operatorname{fan}\left(P, h\right)) \iff ((\exists i \in \operatorname{ZMod}\left(n\right),\; ((i \in P) \land (\operatorname{ear}\left(i\right) = e))) \lor (\exists j \in \operatorname{ZMod}\left(n\right),\; (\neg ((j \in P)) \land (\operatorname{IsDiagonal}\left(\operatorname{symPair}\left(h, j\right)\right) \land (\operatorname{symPair}\left(h, j\right) = e))))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fan is the union of every forced original ear and every original internal root spoke whose other endpoint is outside P. Both parts are finite sets: coincident forced ears and spokes occur once. Vertices retain their original labels.

**Theorem 1.3 (A complete actual triangulation and its ears).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall h \in \operatorname{ZMod}\left(n\right),\; ((6 \leq n) \implies (\operatorname{Independent}\left(P\right) \implies (\neg ((h \in P)) \implies (\operatorname{IsTriangulation}\left(\operatorname{fan}\left(P, h\right)\right) \land ((P \subseteq \operatorname{EarCenters}\left(\operatorname{fan}\left(P, h\right)\right)) \land (\operatorname{EarCenters}\left(\operatorname{fan}\left(P, h\right)\right) \subseteq (P \cup \operatorname{insert}\left((h - 1), \operatorname{insert}\left((h + 1), \emptyset\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan_triangulation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least 6, an independent P and a root outside P give an actual triangulation of the full original polygon. No restriction excludes empty P or forces the root neighbours to survive outside P. Internalness and strict cyclic noncrossing hold for every member. For maximality, an omitted internal chord with a forced endpoint crosses that forced ear. Otherwise, in coordinates relative to the root, let its endpoints be a<b. A surviving centre a+1 supplies a crossing spoke. If a+1 is forced, independence makes a+2 survive; the sole exceptional gap b=a+2 is already the forced ear at a+1. The ear bounds follow from injectivity of original ears and the endpoints of root spokes.

Application to an active matching core. Identify each original ear chord with its centre in ZMod n, and write Ear(T) for the full EarCenters of an actual triangulation T. For n at least 6, let D be cyclically independent, let P and M be disjoint subsets of D with M nonempty, and let U be any actual triangulation with Ear(U) intersect D = M. Define Gamma_D(P) to consist of every original actual triangulation T with Ear(T) intersect D = P. Thus Gamma_D(P) is the underlying chord-set version of ConditionFiber empty empty D P: all outside-D ears and every actual completion are retained. Neither the trace condition on U nor membership in Gamma_D(P) fixes a full ear set.

Choose h in M. The exact trace of U gives h in Ear(U), while disjointness gives h outside P. Independence of D passes to P, so PolygonConditionedFan.fan_triangulation applies to T = fan P h. It supplies an actual triangulation with P contained in Ear(T) and Ear(T) contained in P union {h-1,h+1}. All vertex arithmetic is cyclic on the original polygon. Since h belongs to D, independence of D excludes both neighbours from D. Intersecting the two ear bounds with D therefore gives the exact trace Ear(T) intersect D = P, so T belongs to the complete Gamma_D(P).

The disjointness concerns full ears. PolygonCompressionTrace.earCenters_independent applied to the actual U excludes h-1 and h+1 from Ear(U), because h is an ear of U. No centre of P can lie in Ear(U): it would belong to Ear(U) intersect D = M, contradicting disjointness of P and M. The upper ear bound for T now excludes every possible common ear, including outside D. Hence Ear(T) and Ear(U) are disjoint. They are distinct triangulations: equality would place the known ear h of U in both full ear sets. This argument uses only the fan ear bounds; it does not require Ear(T) = P.

For the original domain, take n at least 14 and a six-element D whose distinct original ear chords are pairwise noncrossing. PolygonCompressionTrace.independent_iff_noncrossing converts that geometric compatibility to the independence used above; the equal-centre case is noncrossing automatically. Let P be a three-ear path trace and M a disjoint two-ear matching trace, both subsets of this D. The argument covers arbitrary compatible placements and every such disjoint path/matching pair, with no additional incidence condition. Let F be one finite family of actual triangulations such that every two distinct members have intersecting full ear sets. An active matching means that some U in this same F has exact D-trace M; its full ear set may be larger than M. The resulting T in Gamma_D(P) cannot belong to F, since T differs from U and their full ear sets are disjoint. Thus Gamma_D(P) is not contained in F, and F intersect Gamma_D(P) is a proper subset of Gamma_D(P). Finset.card_lt_card gives |F intersect Gamma_D(P)| < |Gamma_D(P)|, hence |F intersect Gamma_D(P)| <= |Gamma_D(P)| - 1 both with natural-number subtraction and after converting the cardinalities to signed integers. This includes nonempty selected sides and the case F intersect Gamma_D(P) = empty: the constructed T still makes Gamma_D(P) nonempty. No self-intersection assumption on a single member of F is used.

The original-domain correspondence is the path-fibre non-saturation step in B-37.7 of AURIC_FIB_ATOM_INTRINSIC_CLASSIFICATION_AND_POLYGON_GEOMETRY: its Gamma(P) is Gamma_D(P), a path P = M_i union {x} disjoint from M_j is the selected trace, and a_j > 0 supplies U from the same F with matching trace M = M_j. The source obtains non-saturation using the stronger realization with full ear set exactly P; the existing fan theorem suffices for the implication above. All original completions remain in the fibres. The implication requires no fibre saturation, A > W, protected ears or placement symmetry, and makes no change to the family F.

A local example has n = 14, D = {0,2,4,6,8,10}, P = {0,2,4} and M = {8,10}. Label these six centres f12=0, f34=2, f13=4, f24=6, f14=8 and f23=10. Then P is the path 2-1-3-4 and M is the disjoint matching {f14,f23}. The two distinct actual triangulations U = fan M 11 and V = fan P 13 form a full-ear-intersecting family F = {U,V}: both have the outside-D ear at centre 12. Their exact D-traces are M and P respectively, so the matching core and the selected path side are both nonempty. The application still supplies an omitted member of the full Gamma_D(P). This two-member example makes no assertion that it contains all four prescribed star witnesses of the original problem.

The application establishes only omission and non-saturation with the finite minus-one consequence. It does not supply the complementary path-pair strict/count substitutions or the ell_i >= 2 step. It does not establish all of B-37.7, a partition or deficit identity, a global maximum, an equality classification or a K_res conclusion. It is an application of the cited existing declarations, with no claim of new mathematics.

**Theorem 1.4 (Two distinct original diagonals cross the root ear).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall h \in \operatorname{ZMod}\left(n\right),\; ((6 \leq n) \implies (((\operatorname{card}\left(P\right) + 4) < n) \implies (\exists e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in \operatorname{fan}\left(P, h\right)) \land (\exists f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((f \in \operatorname{fan}\left(P, h\right)) \land (\neg ((e = f)) \land (\operatorname{IsDiagonal}\left(e\right) \land (\operatorname{IsDiagonal}\left(f\right) \land (\operatorname{Cross}\left(e, \operatorname{ear}\left(h\right)\right) \land \operatorname{Cross}\left(f, \operatorname{ear}\left(h\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan_two_crossings` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This stronger statement needs only n at least 6 and |P|+4<n. The complement of P union {h,h-1,h+1} has more than one vertex. Two distinct targets give distinct symmetric-square spokes, each an original internal diagonal crossing ear(h). No count of all triangulation diagonals is used.

**Theorem 1.5 (Positive complete fibres and terminal empty traces).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies (\operatorname{Disjoint}\left(P, Q\right) \implies ((\forall i \in \operatorname{ZMod}\left(n\right),\; \forall j \in \operatorname{ZMod}\left(n\right),\; ((i \in (P \cup Q)) \implies ((j \in (P \cup Q)) \implies (\neg ((i = j)) \implies \neg (\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(j\right)\right)))))) \implies ((((\operatorname{card}\left(P\right) = 2) \land (\operatorname{card}\left(Q\right) = 2)) \lor (((\operatorname{card}\left(P\right) = 3) \land (\operatorname{card}\left(Q\right) = 3)) \lor (((\operatorname{card}\left(P\right) = 2) \land (\operatorname{card}\left(Q\right) = 4)) \lor ((\operatorname{card}\left(P\right) = 4) \land (\operatorname{card}\left(Q\right) = 2))))) \implies (\operatorname{Nonempty}\left(\operatorname{ConditionFiber}\left(P, Q, \emptyset, \emptyset\right)\right) \land ((0 < \operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, \emptyset, \emptyset\right)\right)) \land ((\exists h \in \operatorname{ZMod}\left(n\right),\; (\neg ((h \in P)) \land (\exists T \in \operatorname{ConditionFiber}\left(P, Q, \emptyset, \emptyset\right),\; (\operatorname{val}\left(T\right) = \operatorname{fan}\left(P, h\right))))) \land (\forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((H \subseteq \operatorname{EK}\left((P \cup Q)\right)) \implies ((\forall i \in \operatorname{ZMod}\left(n\right),\; \forall j \in \operatorname{ZMod}\left(n\right),\; ((i \in H) \implies ((j \in H) \implies (\neg ((i = j)) \implies \neg (\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(j\right)\right)))))) \implies (\forall h \in \operatorname{ZMod}\left(n\right),\; ((h \in H) \implies (\exists T \in \operatorname{ConditionFiber}\left(P, Q, H, \emptyset\right),\; ((\operatorname{val}\left(T\right) = \operatorname{fan}\left(P, h\right)) \land (\exists e \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((e \in \operatorname{val}\left(T\right)) \land (\exists f \in \operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right),\; ((f \in \operatorname{val}\left(T\right)) \land (\neg ((e = f)) \land (\operatorname{IsDiagonal}\left(e\right) \land (\operatorname{IsDiagonal}\left(f\right) \land (\operatorname{Cross}\left(e, \operatorname{ear}\left(h\right)\right) \land \operatorname{Cross}\left(f, \operatorname{ear}\left(h\right)\right)))))))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonConditionedFan.source_conditioned_witnesses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

P,Q are disjoint and their union consists of pairwise noncrossing original ears. All four cases (2,2),(3,3),(2,4),(4,2) are included. Independence of P is derived from these geometric conditions. To obtain an actual conditioned completion, choose h outside P union (Q-1) union (Q+1), a set of size at most |P|+2|Q|<n. The root may belong to Q. The literal fan forces P and avoids Q, giving a member of the full ConditionFiber P Q empty empty and positive Nat.card. For every terminal pairwise noncrossing H contained in EK(P union Q) and every h in H, that same fan at h avoids Q union H and has two distinct original internal diagonals crossing ear(h). Thus its exact H trace is empty. ConditionFiber retains every original actual triangulation satisfying its conditions. Exchanging P,Q supplies the opposite direction separately. These are the geometric existence inputs for B-37.2 and the fan paragraph following (37.10), also used in B-34.4. Neither a Catalan count, a flip-image theorem, nor a normalized strict comparison is asserted. EK denotes E_K, Natcard denotes Nat.card, and val is the underlying original chord set.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionedFan.Independent`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan_triangulation`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionedFan.fan_two_crossings`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonConditionedFan.source_conditioned_witnesses`
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarSlide](PolygonEarSlide.md)
