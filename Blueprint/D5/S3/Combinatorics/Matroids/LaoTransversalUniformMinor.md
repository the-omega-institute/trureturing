# A graph criterion for a four-element uniform minor

## Abstract

Full neighborhoods and pair matchings determine which four-element sets support a uniform minor in a bipartite presentation.

**Definition 1.1 (Matchable left sets).**

Lean statement: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.Matchable`

*Formalization.* `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.Matchable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A left set I is matchable if some injection from its vertex subtype to the right type takes every vertex to a neighbor.

**Definition 1.2 (The transversal matroid).**

Lean statement: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.transversal`

*Formalization.* `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.transversal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The matroid on the left type is built from the finite matchable sets. Augmentation follows by increasing agreement between two matchings on their common domain until the larger matching supplies an additional left vertex.

**Theorem 1.3 (The whole left ground).**

$$\forall (L : Type_{u}), \forall (R : Type_{v}), \forall (A : L \to \left(R \to Prop\right)), ground\left(transversal\left(A\right)\right) = univ$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.transversal_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every left vertex is in the ground, including isolated vertices.

**Theorem 1.4 (Independence as matchability).**

$$\forall (L : Type_{u}), \forall (R : Type_{v}), \forall (A : L \to \left(R \to Prop\right)), \forall (I : Set\left(L\right)), (Finite\left(I\right)) \Rightarrow ((Indep\left(transversal\left(A\right), I\right)) \Leftrightarrow (Matchable\left(A, I\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.transversal_indep_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary left and right types, a finite left set is independent exactly when it is matchable. This covers every subset when the left type is finite, including the empty subset, and permits an empty right type.

**Definition 1.5 (Full right neighborhood).**

Lean statement: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.neighborhood`

*Formalization.* `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.neighborhood` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The neighborhood of I contains every right vertex adjacent to any vertex of I.

**Definition 1.6 (The rank-two uniform matroid on four points).**

Lean statement: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.uniform24`

*Formalization.* `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.uniform24` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Its ground is all of Fin 4. Its independent sets are exactly the subsets of cardinality at most two.

**Theorem 1.7 (Uniform minors on a specified four-element ground).**

$$\forall (L : Type_{u}), \forall (R : Type_{v}), [Finite\left(L\right)] [Finite\left(R\right)] \forall (A : L \to \left(R \to Prop\right)), \forall (X : Set\left(L\right)), (ncard\left(X\right) = 4) \Rightarrow ((\exists (N : Matroid\left(L\right)), (IsMinor\left(N, transversal\left(A\right)\right)) \land ((ground\left(N\right) = X) \land (\exists (e : Equiv\left(Subtype\left(ground\left(N\right)\right), Subtype\left((univ : Set\left(Fin\left(4\right)\right))\right)\right)), mapSetEquiv\left(N, e\right) = uniform24))) \Leftrightarrow (\exists (C : Set\left(L\right)), (Disjoint\left(C, X\right)) \land (let B := neighborhood\left(A, (C \cup X)\right); (ncard\left(B\right) = ncard\left(C\right) + 2) \land (\forall (P : Set\left(L\right)), (P \subseteq X) \Rightarrow ((ncard\left(P\right) = 2) \Rightarrow (\exists (f : Subtype\left((C \cup P)\right) \to Subtype\left(B\right)), (Bijective\left(f\right)) \land (\forall (x : Subtype\left((C \cup P)\right)), A\left(x, f\left(x\right)\right))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.has_uniform24_minor_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Hin Lon Lao (2026). *Dynamics of Transversal Matroids*. DOI: [10.48550/arXiv.2611.02586](https://doi.org/10.48550/arXiv.2611.02586). URL: <https://arxiv.org/abs/2611.02586v1>.

*Commentary.*

The relation A runs from the designated left ground L to the presentation indices R. Both types are arbitrary finite types. Fix any four-element left set X. The native matroid minor N must have ground exactly X and a ground equivalence to all of Fin 4 whose relabeling equals the rank-two uniform matroid.

The graph condition chooses a left set C disjoint from the fixed X. The full right neighborhood B of their union must have size |C| + 2. Each two-element subset P of X has an edge-respecting bijection from C ∪ P onto that same B. The bijection may depend on P.

Normalize the minor to a contraction and deletion and choose a basis K of the contracted set. The four surviving vertices are X, and adjoining any pair from X to K gives an independent set. Augmentation rules out a larger matchable subset of K ∪ X. Adding one universal dummy right vertex still falls short of a matching of K ∪ X, so Hall's theorem finds a left subset whose full neighborhood falls short by at least two. This subset must contain all of X. If it omitted a surviving vertex, restricting a suitable pair matching would leave at most one left vertex unmatched. Remove X from the deficient subset to obtain C. The restricted pair matchings give the opposite bound on the size of B, forcing equality and hence bijectivity.

Conversely, contract C and delete the remaining vertices outside X. Extending a subset of X of size at most two to a pair proves its independence after contraction. A larger subset cannot be independent because its required matching would have too many vertices for B. This describes every independent set of the minor and yields the relabeling to Fin 4.

Lao's Question 7.0.2 asks whether any such minor exists. Any minor relabeled to the uniform matroid on Fin 4 has a four-element ground, so applying the equivalence to that ground gives the graph condition. A graph certificate for any four-element X gives the required minor by the reverse implication.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.Matchable`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.has_uniform24_minor_iff`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.neighborhood`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.transversal`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.transversal_ground`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.transversal_indep_iff`
- Truth anchor: `D5/S3/Combinatorics/Matroids/LaoTransversalUniformMinor.uniform24`
