# Alternating reset histories and whole rays

## Abstract

Alternating numbered reset squares yield finite-window tables and a disjoint same-cut decomposition of whole past rays.

NatPositive(q) means 0 < q. Sign is Multiplicative Bool with XOR addition. Matrix means resetMatrix q, Graph means expandedGraph Matrix, and Histories means History Graph with the native product and subtype topologies. The boundary matrix is literally the identity matrix plus Matrix, over the same natural Boolean group algebra. All edge numbers and absolute group coordinates are retained.

The names resetNumberedData, resetFiniteForgetting and resetExpandedEssential denote Alternating.resetNumberedData, Alternating.resetFiniteForgetting and Alternating.reset_expanded_essential in the ResetNumberedHistories namespace. resetAlternatingTablesLocal denotes reset_alternating_tables_local. The other displayed reset names are the same public names in that namespace.

**Definition 1.1 (Uniform alternating table pair on the actual reset graph).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{TablePair}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), 0, q, q, 0\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.resetAlternatingTablePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive q the definition returns TablePair Graph Graph 0 q q 0. Its forward and backward tables read q+1 original numbered edges. The D, F and legal A boundary constructors distinguish identity, reset and advance; the guarded FD/AF squares preserve the endpoints.

**Theorem 1.2 (Even positive q gives the local criterion).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right),\; \operatorname{LocalCriterion}\left(\operatorname{resetAlternatingTablePair}\left(q, hq\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.reset_alternating_tables_local` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive even q, the criterion gives both seams on legal q+2-edge words and both center roundtrips on legal 2q+1-edge words. The left and right comparison ranks contract along their respective sweeps; overlapping strips identify the windows and recover the original center edge.

**Definition 1.3 (Squares on the actual numbered additive boundary).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{resetNumberedData}\left(q, hq\right):\operatorname{NumberedData}\left(\operatorname{resetMatrix}\left(q\right), \operatorname{resetMatrix}\left(q\right), \operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.resetNumberedData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The local square interface uses Edge(identityMatrix + resetMatrix) times Sign as its boundary type. Its source and target are the original expanded boundary endpoints. The two summands occupy disjoint coefficient-number intervals; labels, numbers and absolute signs determine the boundary equivalence.

**Definition 1.4 (Forgetting after q squares).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right),\; \operatorname{resetFiniteForgetting}\left(q, hq, he\right):\operatorname{FiniteForgetting}\left(\operatorname{squares}\left(\operatorname{resetNumberedData}\left(q, hq\right)\right), q\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.resetFiniteForgetting` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

FiniteForgetting is the existing positive-length, left and right forgetting proposition on unrestricted natural-indexed square strips. Equality of the left input strips forces the initial boundaries to coincide after q squares; equality of the right input strips forces the terminal boundaries to coincide. The last common input edge supplies the terminal source equality used by the left contraction.

**Theorem 1.5 (Every positive reset graph is essential).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \operatorname{Essential}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.reset_expanded_essential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every expanded vertex has an outgoing reset edge. Incoming to suffix zero uses reset with the opposite absolute sign; incoming to a positive suffix uses the predecessor advance with the same sign. Positivity is the only hypothesis, so q=1 is included.

**Theorem 1.6 (The square lift equals the finite table map).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right),\; \forall x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right),\; \operatorname{H}\left(\operatorname{squares}\left(\operatorname{resetNumberedData}\left(q, hq\right)\right), \operatorname{resetFiniteForgetting}\left(q, hq, he\right), x\right) = \operatorname{applyTable}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{forward}\left(\operatorname{resetAlternatingTablePair}\left(q, hq\right)\right), \operatorname{seamG}\left(\operatorname{resetAlternatingTablesLocal}\left(q, hq, he\right)\right), x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.reset_generic_H_eq_applyTable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equality holds on every legal bilateral history. A q+1-square window of the full generic lift is compared with the original forward sweep. Both sides retain the same numbered expanded edge at each integer coordinate. forward denotes the f field of the table pair; seamG is the seam field of reset_alternating_tables_local.

**Definition 1.7 (The native history homeomorphism).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right),\; \operatorname{resetAlternatingWholeRayHomeomorph}\left(q, hq, he\right):\operatorname{Homeomorph}\left(\operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.resetAlternatingWholeRayHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is Squares.historyHomeomorph applied to the actual reset numbered data and its q-square finite forgetting. Both histories carry their original product and subtype topology.

**Definition 1.8 (A full representative for each numbered boundary).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right),\; \forall alpha \in \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), n \in Int, r \in \{r:\operatorname{product}\left(\operatorname{Edge}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), Sign\right) | \operatorname{source}\left(\operatorname{expandedGraph}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), r\right) = \operatorname{target}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{coordinate}\left(alpha, n\right)\right)\},\; \operatorname{resetRayRepresentative}\left(q, hq, alpha, n, r\right):\operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.resetRayRepresentative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every positive q, every full history alpha and integer cut n, r is the subtype of full numbered boundary edges with absolute group coordinate whose source equals the target of alpha at n. The representative is NumberedData.beta using the essential reset graph. Its arbitrary legal future extends the prescribed right past; no even hypothesis is needed to define it. A subtype value is denoted value(r).

**Theorem 1.9 (Exact disjoint decomposition and every future preimage).**

$$\forall q \in Nat, hq \in \operatorname{NatPositive}\left(q\right), he \in \operatorname{Even}\left(q\right),\; \forall alpha \in \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right), n \in Int,\; \operatorname{image}\left(\operatorname{resetAlternatingWholeRayHomeomorph}\left(q, hq, he\right), \{y:\operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right) | \forall k \in Int,\; k \le n \Rightarrow \operatorname{coordinate}\left(y, k\right) = \operatorname{coordinate}\left(alpha, k\right)\}\right) = \cup_{r \in \{r:\operatorname{product}\left(\operatorname{Edge}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), Sign\right) | \operatorname{source}\left(\operatorname{expandedGraph}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), r\right) = \operatorname{target}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{coordinate}\left(alpha, n\right)\right)\}} \{y:\operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right) | \forall k \in Int,\; k \le n \Rightarrow \operatorname{coordinate}\left(y, k\right) = \operatorname{coordinate}\left(\operatorname{resetRayRepresentative}\left(q, hq, alpha, n, r\right), k\right)\} \land \left(\left(\forall r \in \{r:\operatorname{product}\left(\operatorname{Edge}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), Sign\right) | \operatorname{source}\left(\operatorname{expandedGraph}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), r\right) = \operatorname{target}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{coordinate}\left(alpha, n\right)\right)\},\; \operatorname{target}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{coordinate}\left(\operatorname{resetRayRepresentative}\left(q, hq, alpha, n, r\right), n\right)\right) = \operatorname{target}\left(\operatorname{expandedGraph}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), \operatorname{value}\left(r\right)\right)\right) \land \left(\left(\forall r \in \{r:\operatorname{product}\left(\operatorname{Edge}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), Sign\right) | \operatorname{source}\left(\operatorname{expandedGraph}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), r\right) = \operatorname{target}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{coordinate}\left(alpha, n\right)\right)\}, s \in \{r:\operatorname{product}\left(\operatorname{Edge}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), Sign\right) | \operatorname{source}\left(\operatorname{expandedGraph}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), r\right) = \operatorname{target}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{coordinate}\left(alpha, n\right)\right)\},\; r \ne s \Rightarrow \operatorname{Disjoint}\left(\{y:\operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right) | \forall k \in Int,\; k \le n \Rightarrow \operatorname{coordinate}\left(y, k\right) = \operatorname{coordinate}\left(\operatorname{resetRayRepresentative}\left(q, hq, alpha, n, r\right), k\right)\}, \{y:\operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right) | \forall k \in Int,\; k \le n \Rightarrow \operatorname{coordinate}\left(y, k\right) = \operatorname{coordinate}\left(\operatorname{resetRayRepresentative}\left(q, hq, alpha, n, s\right), k\right)\}\right)\right) \land \left(\forall r \in \{r:\operatorname{product}\left(\operatorname{Edge}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), Sign\right) | \operatorname{source}\left(\operatorname{expandedGraph}\left(\operatorname{identityMatrix}\left(Sign, q\right) + \operatorname{resetMatrix}\left(q\right)\right), r\right) = \operatorname{target}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right), \operatorname{coordinate}\left(alpha, n\right)\right)\}, y \in \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right),\; \left(\forall k \in Int,\; k \le n \Rightarrow \operatorname{coordinate}\left(y, k\right) = \operatorname{coordinate}\left(\operatorname{resetRayRepresentative}\left(q, hq, alpha, n, r\right), k\right)\right) \Rightarrow \left(\exists x \in \operatorname{History}\left(\operatorname{expandedGraph}\left(\operatorname{resetMatrix}\left(q\right)\right)\right),\; \left(\forall k \in Int,\; k \le n \Rightarrow \operatorname{coordinate}\left(x, k\right) = \operatorname{coordinate}\left(alpha, k\right)\right) \land \left(\operatorname{apply}\left(\operatorname{resetAlternatingWholeRayHomeomorph}\left(q, hq, he\right), x\right) = y \land \operatorname{boundary}\left(\operatorname{leftLift}\left(\operatorname{squares}\left(\operatorname{resetNumberedData}\left(q, hq\right)\right), \operatorname{resetFiniteForgetting}\left(q, hq, he\right), x\right), n\right) = \operatorname{value}\left(r\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.reset_even_same_cut_whole_rays` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every ray in the formula fixes all numbered expanded coordinates at all integers k <= n, including negative times. image is literal set image under the homeomorphism and the union ranges over the exact source-constrained numbered boundary subtype. The four conjuncts state the entire image equality at the same cut, the actual endpoint of every representative, pairwise disjointness for unequal full boundary indices, and a preimage for every legal right future with the original alpha past and exactly that boundary value at n. The preimage boundary is read from Squares.leftLift with the same finite-forgetting proof.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.resetAlternatingTablePair`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.resetAlternatingWholeRayHomeomorph`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.resetFiniteForgetting`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.resetNumberedData`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.resetRayRepresentative`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.reset_alternating_tables_local`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.reset_even_same_cut_whole_rays`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.reset_expanded_essential`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetAlternatingHistories.reset_generic_H_eq_applyTable`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetAlternatingSquares](ResetAlternatingSquares.md)
