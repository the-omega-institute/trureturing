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

For n at least 14, arbitrary P,Q with nonempty union, and finite original families A subset WholeFiber P Q and B subset WholeFiber Q P whose opposite members share an ear, there are one common H subset E_K(P union Q) and families C,D on H. H consists of pairwise noncrossing actual ear chords. C,D are cross-intersecting and closed under every superset inside H.powerset. Their separate complete-fibre P|Q and Q|P masses dominate the respective original cardinalities. Each nonempty side stays nonempty; if both inputs are nonempty, a common output ear proves H nonempty. The empty initial E_K case is included: the same implication excludes two nonempty inputs. Apply the existing exists_terminal_compression to deletionSystem; terminal independence identifies feasible H with the entire powerset. This realizes exactly the compression prefix of B-37.2 residual child 82a336ea36dcb1fdf33de82be432b2ef57a5cccb4770e8737a97a557029cda16, bytes [0,1646), parent bb66dfd880da1b1f58a57a9d778dd6406ce5738d2f047f6862da8c62cf8288f6 bytes [4005,5651). The source cases with cardinalities 2,3,4 and disjoint compatible P,Q are included; those extra assumptions are unnecessary here. Rank/count/Catalan bounds, strictness, total-count positivity, inclusion-exclusion Npq and the normalized bound remain outside this theorem. The construction makes no assertion that every independent trace has a triangulation completion, and no identification of the two weights.

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
