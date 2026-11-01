# Common-support terminal compression of original polygon triangulation families

## Abstract

Common-support terminal compression of original polygon triangulation families

**Definition 1.1 (deletionSystem).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies (\operatorname{Nonempty}\left((P \cup Q)\right) \implies \operatorname{DeletionSystem}\left(\operatorname{EK}\left((P \cup Q)\right)\right)))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.deletionSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For n at least 14 and nonempty P union Q, this constructs the actual DeletionSystem on J=E_K(P union Q). At every H subset J its feasible universe is all independent subsets, its terminal predicate is Independent H, and its left/right weights are respectively weight P Q H and weight Q P H. Nonnegativity is cardinal nonnegativity. feasible_projection and marginal_weight realize all deletion fields. Properness and block_start choose a with a absent and a+1,a+2 present. The coordinates s=a+1,t=a+2,u=a+3 are distinct as required; local_excludes and shift_mem_feasible supply geometry. local_weight_law supplies the left law and, using union_comm on E_K, a separate right law. No weight equality is assumed. The displayed formula gives the constructor type; these field assignments specify its value.

**Definition 1.2 (WholeFiber).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{WholeFiber}\left(P, Q\right) = \operatorname{ConditionFiber}\left(P, Q, \operatorname{empty}\left(\right), \operatorname{empty}\left(\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.WholeFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

WholeFiber P Q is the subtype of all actual triangulations forcing P and forbidding Q, with the vacuous exact trace on the empty observation support. Families are arbitrary finite subsets of this subtype.

**Definition 1.3 (familyTraces).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall A \in \operatorname{Finset}\left(\operatorname{WholeFiber}\left(P, Q\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((X \in \operatorname{familyTraces}\left(H, A\right)) \iff (\exists T \in \operatorname{WholeFiber}\left(P, Q\right),\; ((T \in A) \land (X = \operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{val}\left(T\right)\right), H\right)))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The image contains precisely the observed ear traces of selected original members. It does not replace a partial fibre by a full fibre at the level of the original family.

**Theorem 1.4 (familyTraces feasible).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall A \in \operatorname{Finset}\left(\operatorname{WholeFiber}\left(P, Q\right)\right),\; ((6 \leq n) \implies (\operatorname{familyTraces}\left(H, A\right) \subseteq \operatorname{feasible}\left(H\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every image trace is feasible because each original member is an actual triangulation. Feasible traces without completions remain in the universe.

**Theorem 1.5 (original card le trace mass).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall A \in \operatorname{Finset}\left(\operatorname{WholeFiber}\left(P, Q\right)\right),\; (\operatorname{Realcast}\left(\operatorname{card}\left(A\right)\right) \leq \operatorname{mass}\left(\operatorname{weight}\left(P, Q, H\right), \operatorname{familyTraces}\left(H, A\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.original_card_le_trace_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finset.card_eq_sum_card_image counts original members fibre by fibre. Each selected fibre injects, by retaining its original triangulation, into the complete ConditionFiber P Q H X. Summing the cardinal bounds gives an inequality. No saturation equality is asserted, and no global positivity or explicit conditional-count formula is needed.

**Theorem 1.6 (shared ear mem EK).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall T \in \operatorname{WholeFiber}\left(P, Q\right),\; \forall U \in \operatorname{WholeFiber}\left(Q, P\right),\; \forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in \operatorname{EarCenters}\left(\operatorname{val}\left(T\right)\right)) \implies ((i \in \operatorname{EarCenters}\left(\operatorname{val}\left(U\right)\right)) \implies (i \in \operatorname{EK}\left((P \cup Q)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.shared_ear_mem_EK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A common ear cannot lie in P or Q, since the opposite member forbids that side. For every k in P use noncrossing in the first triangulation, and for k in Q use the second. Thus the common ear avoids all K ears and belongs to the full allowed E_K K.

**Theorem 1.7 (common ears eq trace inter).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall T \in \operatorname{WholeFiber}\left(P, Q\right),\; \forall U \in \operatorname{WholeFiber}\left(Q, P\right),\; (\operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{val}\left(T\right)\right), \operatorname{EarCenters}\left(\operatorname{val}\left(U\right)\right)\right) = \operatorname{inter}\left(\operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{val}\left(T\right)\right), \operatorname{EK}\left((P \cup Q)\right)\right), \operatorname{inter}\left(\operatorname{EarCenters}\left(\operatorname{val}\left(U\right)\right), \operatorname{EK}\left((P \cup Q)\right)\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.common_ears_eq_trace_inter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the full-ear to trace-intersection bridge (source 37.5). It uses the complete E_K(P union Q), rather than a protected subcarrier chosen in advance.

**Theorem 1.8 (familyTraces cross).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall A \in \operatorname{Finset}\left(\operatorname{WholeFiber}\left(P, Q\right)\right),\; \forall B \in \operatorname{Finset}\left(\operatorname{WholeFiber}\left(Q, P\right)\right),\; ((\forall T \in \operatorname{WholeFiber}\left(P, Q\right),\; ((T \in A) \implies (\forall U \in \operatorname{WholeFiber}\left(Q, P\right),\; ((U \in B) \implies \neg (\operatorname{Disjoint}\left(\operatorname{EarCenters}\left(\operatorname{val}\left(T\right)\right), \operatorname{EarCenters}\left(\operatorname{val}\left(U\right)\right)\right)))))) \implies \operatorname{CrossIntersecting}\left(\operatorname{familyTraces}\left(\operatorname{EK}\left((P \cup Q)\right), A\right), \operatorname{familyTraces}\left(\operatorname{EK}\left((P \cup Q)\right), B\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces_cross` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Full-ear cross-intersection of opposite original members descends to cross-intersection of their allowed traces, by the exact intersection bridge.

**Theorem 1.9 (exists original terminal compression).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall A \in \operatorname{Finset}\left(\operatorname{WholeFiber}\left(P, Q\right)\right),\; \forall B \in \operatorname{Finset}\left(\operatorname{WholeFiber}\left(Q, P\right)\right),\; ((14 \leq n) \implies (\operatorname{Nonempty}\left((P \cup Q)\right) \implies ((\forall T \in \operatorname{WholeFiber}\left(P, Q\right),\; ((T \in A) \implies (\forall U \in \operatorname{WholeFiber}\left(Q, P\right),\; ((U \in B) \implies \neg (\operatorname{Disjoint}\left(\operatorname{EarCenters}\left(\operatorname{val}\left(T\right)\right), \operatorname{EarCenters}\left(\operatorname{val}\left(U\right)\right)\right)))))) \implies (\exists H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \exists C \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \exists D \in \operatorname{Finset}\left(\operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; ((H \subseteq \operatorname{EK}\left((P \cup Q)\right)) \land (\operatorname{Independent}\left(H\right) \land ((\forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in H) \implies (\forall j \in \operatorname{ZMod}\left(n\right),\; ((j \in H) \implies \neg (\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(j\right)\right)))))) \land ((C \subseteq \operatorname{powerset}\left(H\right)) \land ((D \subseteq \operatorname{powerset}\left(H\right)) \land (\operatorname{CrossIntersecting}\left(C, D\right) \land (\operatorname{RelativelyUpper}\left(\operatorname{powerset}\left(H\right), C\right) \land (\operatorname{RelativelyUpper}\left(\operatorname{powerset}\left(H\right), D\right) \land ((\operatorname{Realcast}\left(\operatorname{card}\left(A\right)\right) \leq \operatorname{mass}\left(\operatorname{weight}\left(P, Q, H\right), C\right)) \land ((\operatorname{Realcast}\left(\operatorname{card}\left(B\right)\right) \leq \operatorname{mass}\left(\operatorname{weight}\left(Q, P, H\right), D\right)) \land ((\operatorname{Nonempty}\left(A\right) \implies \operatorname{Nonempty}\left(C\right)) \land ((\operatorname{Nonempty}\left(B\right) \implies \operatorname{Nonempty}\left(D\right)) \land (\operatorname{Nonempty}\left(A\right) \implies (\operatorname{Nonempty}\left(B\right) \implies \operatorname{Nonempty}\left(H\right)))))))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.exists_original_terminal_compression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least 14, arbitrary P,Q with nonempty union, and finite original families A subset WholeFiber P Q and B subset WholeFiber Q P whose opposite members share an ear, there are one common H subset E_K(P union Q) and families C,D on H. H consists of pairwise noncrossing actual ear chords. C,D are cross-intersecting and closed under every superset inside H.powerset. Their separate complete-fibre P|Q and Q|P masses dominate the respective original cardinalities. Each nonempty side stays nonempty; if both inputs are nonempty, a common output ear proves H nonempty. The empty initial E_K case is included: the same implication excludes two nonempty inputs. Apply the existing exists_terminal_compression to deletionSystem; terminal independence identifies feasible H with the entire powerset. This gives simultaneous terminal compression for the two original families. The source cases with cardinalities 2,3,4 and disjoint compatible P,Q are included; those extra assumptions are unnecessary here. Rank/count/Catalan bounds, strictness, total-count positivity, inclusion-exclusion Npq and the normalized bound remain outside this theorem. The construction makes no assertion that every independent trace has a triangulation completion, and no identification of the two weights.

Application to actual radial weights on the common terminal support. Fix n at least 14 with NeZero n, arbitrary finite P,Q of ZMod n with Disjoint P Q, Compatible(P union Q), and nonempty union. Let A be any finite subset of WholeFiber P Q and B any finite subset of WholeFiber Q P, with every T in A and U in B sharing an actual ear. Invoke exists_original_terminal_compression once and fix its single output H,C,D throughout. Its original premises require neither disjointness nor compatibility of P,Q; those are extra assumptions of this counting application. The original thirteen conclusions all remain attached to these same witnesses: support in E_K(P union Q), independence and pairwise noncrossing of H; both powerset inclusions, cross-intersection, both relative-upperness properties, both original-cardinality mass bounds, both one-sided nonemptiness implications, and nonemptiness of H when both inputs are nonempty. No input family is replaced by a saturated family.

For each X subset this H, consider the complete actual trace fibre ConditionFiber P Q H X. By the native ConditionFiber definition, its members are all original chord sets T satisfying IsTriangulation T, P subset EarCenters(T), Disjoint Q (EarCenters(T)), and EarCenters(T) intersect H = X. Keeping exactly the same T gives an equivalence with WholeFiber(P union X)(Q union(H minus X)); the inverse also keeps T. The trace equation forces X and forbids H minus X. Conversely, forcing X and forbidding H minus X makes the trace exactly X because X subset H. The same correspondence holds with P,Q interchanged:

$\forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((X \subseteq H) \implies (\operatorname{Nonempty}\left(\operatorname{Equiv}\left(\operatorname{ConditionFiber}\left(P, Q, H, X\right), \operatorname{WholeFiber}\left((P \cup X), (Q \cup \operatorname{sdiff}\left(H, X\right))\right)\right)\right) \land \operatorname{Nonempty}\left(\operatorname{Equiv}\left(\operatorname{ConditionFiber}\left(Q, P, H, X\right), \operatorname{WholeFiber}\left((Q \cup X), (P \cup \operatorname{sdiff}\left(H, X\right))\right)\right)\right)))$

This identity on triangulations preserves every completion and every ear outside H subject to the original P,Q restrictions. Distinct triangulations with the same trace stay distinct, so their full multiplicities are counted. The correspondence also preserves impossible or empty fibres, whose cardinalities are zero; it needs only X subset H, without geometric or realizability assumptions. In particular H empty and X empty give the original whole fibres, while X=H forces all of H and adds no forbidden centre from H. No representative, quotient, product decomposition, or completion choice is involved.

To apply PolygonConditionalCounts.conditional_card, the enlarged forced and forbidden sets must be disjoint and their union compatible. These conditions follow at the actual returned support: E_K(P union Q) excludes P union Q and makes each H ear noncrossing with every P or Q ear. Original compatibility handles pairs in P union Q, the terminal noncrossing conclusion handles pairs in H, and the E_K condition, with symmetry of crossing, handles mixed pairs. Thus P union X and Q union(H minus X) are disjoint and their union is the compatible set P union Q union H. Interchanging P,Q supplies the other orientation with the same H and X, rather than another placement.

Write p=card(P), q=card(Q), h=card(H), and for each X subset H write x=card(X). Disjointness gives card(P union X)=p+x and card(Q union(H minus X))=q+(h-x); here h-x is natural subtraction and x<=h. Apply conditional_card to those enlarged sets and transport Nat.card along the displayed identity on T. This gives the following exact integer counts for every X subset H; Npq is the native integer alternating Catalan sum, with its native natural index subtractions:

$\forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((X \subseteq H) \implies (((\operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, H, X\right)\right): \mathbb{Z}) = \operatorname{Npq}\left(n, (p + \operatorname{card}\left(X\right)), (q + (h - \operatorname{card}\left(X\right)))\right)) \land ((\operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(Q, P, H, X\right)\right): \mathbb{Z}) = \operatorname{Npq}\left(n, (q + \operatorname{card}\left(X\right)), (p + (h - \operatorname{card}\left(X\right)))\right))))$

PolygonCompressionTrace.weight is the real cast of the complete trace-fibre Nat.card. Casting the two integer equalities to the reals therefore identifies the actual weights exactly. Realcast below denotes the cast into the reals, including the integer-to-real cast of Npq. No division, normalization, or positive-total hypothesis is used:

$\forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((X \subseteq H) \implies ((\operatorname{weight}\left(P, Q, H, X\right) = \operatorname{Realcast}\left(\operatorname{Npq}\left(n, (p + \operatorname{card}\left(X\right)), (q + (h - \operatorname{card}\left(X\right)))\right)\right)) \land (\operatorname{weight}\left(Q, P, H, X\right) = \operatorname{Realcast}\left(\operatorname{Npq}\left(n, (q + \operatorname{card}\left(X\right)), (p + (h - \operatorname{card}\left(X\right)))\right)\right))))$

The native mass definition sums weights over a family. Every X in the fixed C or D is a subset of this H by the original powerset conclusions, so substitute the corresponding pointwise equality in each summand. The original separate mass bounds then become exact radial-sum bounds on the same C,D:

$(\operatorname{mass}\left(\operatorname{weight}\left(P, Q, H\right), C\right) = \sum _{X\in C} \operatorname{Realcast}\left(\operatorname{Npq}\left(n, (p + \operatorname{card}\left(X\right)), (q + (h - \operatorname{card}\left(X\right)))\right)\right))$

$(\operatorname{mass}\left(\operatorname{weight}\left(Q, P, H\right), D\right) = \sum _{X\in D} \operatorname{Realcast}\left(\operatorname{Npq}\left(n, (q + \operatorname{card}\left(X\right)), (p + (h - \operatorname{card}\left(X\right)))\right)\right))$

$(\operatorname{Realcast}\left(\operatorname{card}\left(A\right)\right) \leq \sum _{X\in C} \operatorname{Realcast}\left(\operatorname{Npq}\left(n, (p + \operatorname{card}\left(X\right)), (q + (h - \operatorname{card}\left(X\right)))\right)\right))$

$(\operatorname{Realcast}\left(\operatorname{card}\left(B\right)\right) \leq \sum _{X\in D} \operatorname{Realcast}\left(\operatorname{Npq}\left(n, (q + \operatorname{card}\left(X\right)), (p + (h - \operatorname{card}\left(X\right)))\right)\right))$

Radial here means that, for fixed P,Q,H, each weight depends on X through card(X). The two orientations retain their respective Npq arguments; this does not identify their weights, assert that C,D are determined by ranks, or turn either mass bound into equality for the original A,B. Empty C or D contributes the empty sum. Impossible trace fibres contribute zero with their full cardinal interpretation, without imposing positivity on H, A, B, C, D, any fibre, or any total.

The same enlarged compatible union has cardinality p+q+h, since P,Q,H are pairwise disjoint. PolygonEarContraction.compatible_card_bound applies because n>=14 implies n>=6, and gives the legal carrier bound on this actual H. Substitution of p=q=2 gives its two-by-two specialization:

$((2 \cdot ((p + q) + h)) \leq n)$

$((p = 2) \implies ((q = 2) \implies ((2 \cdot (h + 4)) \leq n)))$

These are unnormalized counts and bounds at the returned common support. Partition and normalization, an adjacent-ratio estimate for the actual Npq weights, actual cutoffs or an alternative completion route, same-F deficits, and the global all-n theorem remain unresolved. Neither positive total counts, the normalized inequality and its equality classification, nor a new completion or placement principle follows from this application.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.WholeFiber`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.common_ears_eq_trace_inter`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.deletionSystem`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.exists_original_terminal_compression`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces_cross`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.familyTraces_feasible`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.original_card_le_trace_mass`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonSimultaneousCompression.shared_ear_mem_EK`
- Dependency: [D5/S3/Geometry/Polygons/PolygonCompressionTrace](PolygonCompressionTrace.md)
