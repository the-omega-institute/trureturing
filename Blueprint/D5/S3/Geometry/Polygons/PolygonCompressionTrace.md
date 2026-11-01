# Actual cyclic geometry, independent trace universes and complete-fibre deletion

## Abstract

Actual cyclic geometry, independent trace universes and complete-fibre deletion

**Definition 1.1 (Independent).**

$$\forall n \in Nat,\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Independent}\left(H\right) \iff (\forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in H) \implies \neg (((i + 1) \in H)))))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonCompressionTrace.Independent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Independent means no adjacent cyclic centres, including across the cyclic boundary.

**Definition 1.2 (feasible).**

$$\forall n \in Nat,\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((X \in \operatorname{feasible}\left(H\right)) \iff ((X \subseteq H) \land \operatorname{Independent}\left(X\right)))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonCompressionTrace.feasible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The universe contains every independent subset of H. It includes impossible traces; no completion is selected or required.

**Definition 1.3 (weight).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{weight}\left(P, Q, H, X\right) = \operatorname{Realcast}\left(\operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, H, X\right)\right)\right))$$

*Formalization.* `D5/S3/Geometry/Polygons/PolygonCompressionTrace.weight` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real weight is Nat.card of the entire ConditionFiber P Q H X subtype: every finite maximal noncrossing diagonal carrier with P forced, Q forbidden and exact ear trace X on H. All chords outside H are retained.

**Theorem 1.4 (mem feasible).**

$$\forall n \in Nat,\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((X \in \operatorname{feasible}\left(H\right)) \iff ((X \subseteq H) \land \operatorname{Independent}\left(X\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.mem_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Membership exposes both the support and cyclic independence requirements.

**Theorem 1.5 (independent subset).**

$$\forall n \in Nat,\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Independent}\left(H\right) \implies ((X \subseteq H) \implies \operatorname{Independent}\left(X\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.independent_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cyclic independence passes to subsets, and is used for actual traces and deletion.

**Theorem 1.6 (cross ear iff adjacent).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall i \in \operatorname{ZMod}\left(n\right),\; \forall j \in \operatorname{ZMod}\left(n\right),\; ((6 \leq n) \implies (\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(j\right)\right) \iff ((j = (i + 1)) \lor (i = (j + 1)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.cross_ear_iff_adjacent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least 6 the actual strict cyclic crossing of ear chords occurs exactly at adjacent centres. Translate i to 1, apply the existing crossing endpoint lemma, then use symmetric-pair endpoint equality; the converse is transported from local_crossings. No abstract replacement of the geometric crossing relation is made.

**Theorem 1.7 (earCenters independent).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; ((6 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies \operatorname{Independent}\left(\operatorname{EarCenters}\left(T\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.earCenters_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every actual triangulation has an independent set of ear centres, by noncrossing of its chord carrier.

**Theorem 1.8 (block start).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\neg ((H = \operatorname{univ}\left(\right))) \implies ((\exists b \in \operatorname{ZMod}\left(n\right),\; ((b \in H) \land ((b + 1) \in H))) \implies (\exists a \in \operatorname{ZMod}\left(n\right),\; (\neg ((a \in H)) \land (((a + 1) \in H) \land ((a + 2) \in H))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.block_start` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every proper support containing an adjacent pair has a cyclic block start a absent from H with a+1,a+2 present. If none existed, predecessors of each adjacent pair would be present. Induction gives b-k,b+1-k in H for all natural k, and k=(b-z).val reaches any z, contradicting properness. This lemma needs only NeZero n.

**Theorem 1.9 (trace mem feasible).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall T \in \operatorname{Finset}\left(\operatorname{Sym2}\left(\operatorname{ZMod}\left(n\right)\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((6 \leq n) \implies (\operatorname{IsTriangulation}\left(T\right) \implies (\operatorname{inter}\left(\operatorname{EarCenters}\left(T\right), H\right) \in \operatorname{feasible}\left(H\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.trace_mem_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact ear trace of each actual triangulation belongs to the full independent-subset universe.

**Theorem 1.10 (weight zero of not feasible).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((6 \leq n) \implies (\neg ((X \in \operatorname{feasible}\left(H\right))) \implies (\operatorname{weight}\left(P, Q, H, X\right) = 0)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.weight_zero_of_not_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A trace outside the feasible universe has empty actual fibre, hence zero raw weight. This removes infeasible extension terms without asserting realizability of feasible traces.

**Theorem 1.11 (feasible projection).**

$$\forall n \in Nat,\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall t \in \operatorname{ZMod}\left(n\right),\; (\operatorname{imageErase}\left(\operatorname{feasible}\left(H\right), t\right) = \operatorname{feasible}\left(\operatorname{erase}\left(H, t\right)\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.feasible_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Deleting t maps the full feasible trace family exactly onto the family on H minus t. In reverse, R itself is a preimage; insertion of t need not be feasible.

**Theorem 1.12 (condition fibre card delete).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall t \in \operatorname{ZMod}\left(n\right),\; ((t \in H) \implies (\neg ((t \in R)) \implies (\operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, \operatorname{erase}\left(H, t\right), R\right)\right) = (\operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, H, R\right)\right) + \operatorname{Natcard}\left(\operatorname{ConditionFiber}\left(P, Q, H, \operatorname{insert}\left(t, R\right)\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.condition_fibre_card_delete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The entire reduced observation fibre is partitioned by whether t is an ear. Both equivalences retain the same original chord set and all forced/forbidden conditions. This is an equality of raw cardinalities, with no lower bound on n and no nonempty-completion premise.

**Theorem 1.13 (marginal weight).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall R \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall t \in \operatorname{ZMod}\left(n\right),\; ((6 \leq n) \implies ((t \in H) \implies ((R \in \operatorname{feasible}\left(\operatorname{erase}\left(H, t\right)\right)) \implies (\operatorname{marginalWeight}\left(\operatorname{feasible}\left(H\right), \operatorname{weight}\left(P, Q, H\right), t, R\right) = \operatorname{weight}\left(P, Q, \operatorname{erase}\left(H, t\right), R\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.marginal_weight` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite projection fibre consists of R and insert(t,R) when the latter is feasible. The complete-cardinality partition and zero weight of infeasible traces identify its sum with the actual reduced weight. This law is applied separately to P|Q and Q|P.

**Theorem 1.14 (proper of subset EK).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall K \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Nonempty}\left(K\right) \implies ((H \subseteq \operatorname{EK}\left(K\right)) \implies \neg ((H = \operatorname{univ}\left(\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.proper_of_subset_EK` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Any member k of nonempty K is excluded from E_K K, so every support contained in E_K K is proper.

**Theorem 1.15 (feasible of independent).**

$$\forall n \in Nat,\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\operatorname{Independent}\left(H\right) \implies (\operatorname{feasible}\left(H\right) = \operatorname{powerset}\left(H\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.feasible_of_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a terminal independent support, every subset is feasible; zero actual weights may still occur.

**Theorem 1.16 (shift mem feasible).**

$$\forall n \in Nat,\; \forall a \in \operatorname{ZMod}\left(n\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; (\neg ((a \in H)) \implies (((a + 1) \in H) \implies ((X \in \operatorname{feasible}\left(H\right)) \implies (\operatorname{shift}\left((a + 1), (a + 2), X\right) \in \operatorname{feasible}\left(H\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.shift_mem_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At a block start, replacing a+2 by a+1 stays feasible. A newly adjacent predecessor would have to be a, which is absent from H; the successor a+2 was deleted.

**Theorem 1.17 (local excludes).**

$$\forall n \in Nat,\; \forall a \in \operatorname{ZMod}\left(n\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((X \in \operatorname{feasible}\left(H\right)) \implies (((a + 2) \in X) \implies (\neg (((a + 1) \in X)) \land \neg (((a + 3) \in X)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.local_excludes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A feasible trace containing a+2 omits both adjacent centres a+1 and a+3.

**Theorem 1.18 (local weight law).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall a \in \operatorname{ZMod}\left(n\right),\; \forall P \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall Q \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; \forall X \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((14 \leq n) \implies ((H \subseteq \operatorname{EK}\left((P \cup Q)\right)) \implies (\neg ((a \in H)) \implies (((a + 1) \in H) \implies (((a + 2) \in H) \implies ((X \in \operatorname{feasible}\left(H\right)) \implies (((a + 2) \in X) \implies (\operatorname{weight}\left(P, Q, H, X\right) = (\operatorname{weight}\left(P, Q, H, \operatorname{shift}\left((a + 1), (a + 2), X\right)\right) + \operatorname{ite}\left((\operatorname{insert}\left((a + 3), \operatorname{shift}\left((a + 1), (a + 2), X\right)\right) \in \operatorname{feasible}\left(H\right)), \operatorname{weight}\left(P, Q, H, \operatorname{insert}\left((a + 3), \operatorname{shift}\left((a + 1), (a + 2), X\right)\right)\right), 0\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.local_weight_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use the merged condition_fibre_card_at with R=X minus a+2. The local exclusions give its required support. Its optional branch tests a+3 in H, whereas generic compression tests feasibility of the extended trace. If the extension is infeasible its complete fibre is empty, including when a+4 is already present. If a+3 is outside H the extension is outside H as well. Thus the two tests give the same weighted equation for all traces, including impossible ones.

**Theorem 1.19 (independent iff noncrossing).**

$$\forall n \in Nat,\; [\operatorname{NeZero}\left(n\right)], \forall H \in \operatorname{Finset}\left(\operatorname{ZMod}\left(n\right)\right),\; ((6 \leq n) \implies (\operatorname{Independent}\left(H\right) \iff (\forall i \in \operatorname{ZMod}\left(n\right),\; ((i \in H) \implies (\forall j \in \operatorname{ZMod}\left(n\right),\; ((j \in H) \implies \neg (\operatorname{Cross}\left(\operatorname{ear}\left(i\right), \operatorname{ear}\left(j\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/PolygonCompressionTrace.independent_iff_noncrossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The terminal predicate is exactly pairwise noncrossing of actual ear chords, not a completion-existence criterion.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.Independent`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.block_start`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.condition_fibre_card_delete`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.cross_ear_iff_adjacent`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.earCenters_independent`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.feasible`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.feasible_of_independent`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.feasible_projection`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.independent_iff_noncrossing`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.independent_subset`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.local_excludes`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.local_weight_law`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.marginal_weight`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.mem_feasible`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.proper_of_subset_EK`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.shift_mem_feasible`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.trace_mem_feasible`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.weight`
- Truth anchor: `D5/S3/Geometry/Polygons/PolygonCompressionTrace.weight_zero_of_not_feasible`
- Dependency: [D5/S3/Combinatorics/SetFamily/SimultaneousCompression](../../Combinatorics/SetFamily/SimultaneousCompression.md)
- Dependency: [D5/S3/Geometry/Polygons/PolygonEarSlideCardinality](PolygonEarSlideCardinality.md)
