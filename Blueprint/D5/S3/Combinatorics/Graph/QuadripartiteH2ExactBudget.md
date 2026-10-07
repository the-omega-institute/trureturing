# Four-cube exact degree-two repair budget

## Abstract

The minimum triangular support after an edge repair equals the minimum total four-coordinate Hamming cost of an unordered pairing of the tetrahedral defects.

**Definition 1.1 (The dual cube).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.cubeGraph`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.cubeGraph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cube is Bool^4, represented by four Boolean coordinates. The fixed simple graph cubeGraph joins exactly the pairs at Hamming distance one. Face is Fin 4 times Bool^3 and indexes the actual unordered triangular faces of the boundary of the four-dimensional cross-polytope.

**Definition 1.2 (The positive endpoint of a dual edge).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.insertOne`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.insertOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

insertOne(i,t) inserts true in coordinate i of the three-coordinate sign vector t. The existing insertZero inserts false in that coordinate.

**Definition 1.3 (The actual face-to-edge map).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.dualEdge`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.dualEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

dualEdge(f) is the unordered pair of insertZero(f.1,f.2) and insertOne(f.1,f.2). These two tetrahedra are incident to the face f.

**Definition 1.4 (Supported dual edges).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.supportEdges`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.supportEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a binary triangular cochain F:Face -> ZMod 2, supportEdges(F) is the image under dualEdge of the nonzero faces. Its cardinality is exactly the support weight of F.

**Definition 1.5 (Tetrahedral defects).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.syndrome`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.syndrome` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

syndrome(F) consists of the vertices b for which d2(F)(b) is nonzero. The tetrahedral defect d2(F)(b) sums the four incident triangular values in ZMod 2.

**Definition 1.6 (Odd terminals of a support).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.oddTerminals`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.oddTerminals` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

oddTerminals(E) consists of the cube vertices incident to an odd number of edges of E. Incidences count each supported edge once.

**Definition 1.7 (A simple path piece).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.PathPiece`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.PathPiece` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A PathPiece has two distinct cube endpoints and a walk in the fixed cube graph with no repeated vertices. It therefore repeats no edges.

**Definition 1.8 (A simple even cycle piece).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.CyclePiece`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.CyclePiece` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A CyclePiece is a nonempty closed trail in the fixed cube graph whose only repeated vertex is its base, together with evenness of its length.

**Definition 1.9 (Exact support and terminal partition).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.supportCertificate`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.supportCertificate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite E, a list ps of PathPiece values and a list cs of CyclePiece values form a supportCertificate when the concatenated path and cycle edge lists are a permutation of E.toList, the concatenated path endpoint lists are a permutation of oddTerminals(E).toList, the sum of all path and cycle lengths equals E.card, and the sum of endpoint Hamming distances is at most the sum of path lengths. The first permutation accounts for every edge exactly once, including all discarded cycles, and gives pairwise edge disjointness. The second permutation assigns each terminal exactly once. Paths may share vertices; a terminal may be internal to another path.

**Definition 1.10 (Cost of one unordered pair).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.pairCost`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.pairCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pairCost is the four-coordinate Hamming distance lifted to Sym2 Cube. Symmetry makes this independent of an ordering of the two vertices.

**Definition 1.11 (Total pairing cost).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.pairingCost`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.pairingCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

pairingCost(P) sums pairCost over the finite list P. The empty list has cost zero.

**Definition 1.12 (An unordered pairing).**

Lean statement: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.IsPairing`

*Formalization.* `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.IsPairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

IsPairing(S,P) requires every Sym2 Cube value in P to be nondiagonal and the concatenation of their two-element vertex subsets to be a permutation of S.toList. Thus these unordered two-element subsets partition S, with every vertex appearing once. The order of the subsets carries no mathematical information.

**Theorem 1.13 (Exact support certificate and repair budget).**

$$(Injective(dualEdge)) \land ((\forall f \in Face,\; dualEdge(f) \in edgeSet(cubeGraph)) \land ((\forall E \in Finset(Sym2(Cube)),\; (E \subseteq edgeSet(cubeGraph)) \Rightarrow (\exists ps \in List(PathPiece),\; \exists cs \in List(CyclePiece),\; supportCertificate(E,ps,cs))) \land ((\forall F \in Cochain,\; (card(supportEdges(F)) = weight(F)) \land (oddTerminals(supportEdges(F)) = syndrome(F))) \land ((\forall F \in Cochain,\; \forall k \in Nat,\; (\exists e \in EdgeCochain,\; weight(F+d1(e)) \le k) \Leftrightarrow (\exists P \in List(Sym2(Cube)),\; (IsPairing(syndrome(F),P)) \land (pairingCost(P) \le k))) \land (\forall e \in EdgeCochain,\; 4 \le weight(path+d1(e)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.fourcube_exact_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The face-to-edge map is injective and takes every actual triangle to a cube edge. Every finite cube edge support E has the full path and even-cycle certificate defined above. For every cochain F, supportEdges(F).card equals weight(F), and its odd terminals equal syndrome(F).

For every binary triangular cochain F and every natural budget k, an edge cochain e with weight(F+d1(e)) <= k exists if and only if syndrome(F) has an unordered pairing P with pairingCost(P) <= k. This includes empty syndromes and k=0. The edge cochain uses the existing simplicial coboundary d1 on the actual triangular faces.

Choose a globally longest trail in the remaining support. Its endpoints exhaust their incident support edges. If they differ, trail parity makes them odd terminals, and a simple path between them can be removed. If they agree, remove a nonempty simple cycle from the trail. The cube's Boolean coloring makes every closed walk even. Induction on the remaining support preserves the edge partition, the terminal partition, and the exact total length. The triangle inequality bounds endpoint Hamming costs by path lengths.

For a repair, apply that certificate to the repaired support; d2(d1(e))=0 preserves the original syndrome. Conversely, sum the existing coordinate geodesics for the paired terminals. Their boundaries add to the syndrome and their weights sum to the pairing cost, with cancellation only reducing support. The existing universal repair theorem with p=2 and q=1, applied to F plus this filling with zero defect, supplies the edge cochain.

The existing four-face antipodal path has weight four and two antipodal defects. Every edge repair still has weight at least four, as given by the existing octahedral sharpness theorem. The shortest-path parity mechanism is described by Edmonds and Johnson (1973), Section 3, pages 90-93. The support-count convention and coefficient-two bound are described by Dotterrer and Kahle, arXiv:1012.5316v2, Definitions 2.6 and 2.8 and Proposition 5.5.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.CyclePiece`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.IsPairing`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.PathPiece`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.cubeGraph`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.dualEdge`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.fourcube_exact_budget`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.insertOne`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.oddTerminals`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.pairCost`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.pairingCost`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.supportCertificate`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.supportEdges`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadripartiteH2ExactBudget.syndrome`
- Dependency: [D5/S3/Combinatorics/Graph/QuadripartiteH2Repair](QuadripartiteH2Repair.md)
