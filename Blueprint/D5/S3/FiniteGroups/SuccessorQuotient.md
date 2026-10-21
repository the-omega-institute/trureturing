# A canonical quotient of a directed relation

## Abstract

The least successor-compatible quotient controls both assignments and all relation symmetries.

The relation R may contain loops. An admissible equivalence puts all successors of one vertex in one class, and puts successors of equivalent vertices in equivalent classes. Intersecting all such equivalences gives the least one. PositiveOutdegree(R) means every x has some y with R(x,y); PositiveIndegree(R) means every y has some x with R(x,y). Positive outdegree defines the successor on its classes; positive indegree makes that successor onto. On a finite vertex type the successor is therefore a permutation beta.

**Definition 1.1 (Exact descent of assignments).**

$$\forall V \in Typeu,\; \forall R \in V \to \left(V \to Prop\right),\; \forall K \in Typeu,\; \forall u \in K \to K,\; \operatorname{PositiveOutdegree}\left(R\right) \Rightarrow \operatorname{Equiv}\left(\operatorname{Assignments}\left(R, u\right), \operatorname{QuotientAssignments}\left(R, u\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/SuccessorQuotient.assignmentEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Assignments satisfy t(y)=u(t(x)) on every arrow x to y. Their equality relation is admissible directly from these equations. They consequently descend uniquely to the least quotient. Pullback is the inverse; no constancy hypothesis is assumed.

**Theorem 1.2 (Functorial successor).**

$$\forall V \in Typeu,\; \forall R \in V \to \left(V \to Prop\right),\; \operatorname{PositiveOutdegree}\left(R\right) \Rightarrow \left(\forall g \in \operatorname{relationAut}\left(R\right),\; \forall q \in \operatorname{Blocks}\left(R\right),\; \operatorname{blockHom}\left(R, g, \operatorname{successor}\left(R, q\right)\right) = \operatorname{successor}\left(R, \operatorname{blockHom}\left(R, g, q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SuccessorQuotient.block_successor_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every relation automorphism preserves the least equivalence and induces a permutation of its classes. This induced action commutes with the successor.

**Definition 1.3 (The actual block-action kernel).**

$$\forall V \in Typeu,\; \forall R \in V \to \left(V \to Prop\right),\; \operatorname{ker}\left(\operatorname{blockHom}\left(R\right)\right) \to \left(\forall q \in \operatorname{Blocks}\left(R\right),\; \operatorname{Perm}\left(\operatorname{Fiber}\left(R, q\right)\right)\right)$$

*Formalization.* `D5/S3/FiniteGroups/SuccessorQuotient.kernelRestriction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

An element of the kernel preserves each actual fiber of the quotient map, so restriction defines a permutation of each fiber. These restrictions together determine the original permutation. The action on classes need not be faithful.

**Theorem 1.4 (The centralizer and fiber bound).**

$$\forall V \in Typeu,\; \forall R \in V \to \left(V \to Prop\right),\; \left(\operatorname{Finite}\left(V\right) \land \left(\operatorname{PositiveOutdegree}\left(R\right) \land \operatorname{PositiveIndegree}\left(R\right)\right)\right) \Rightarrow \operatorname{card}\left(\operatorname{relationAut}\left(R\right)\right) \le \operatorname{card}\left(\operatorname{centralizer}\left(\operatorname{beta}\left(R\right)\right)\right) \cdot \operatorname{card}\left(\operatorname{BlockPermutationProduct}\left(R\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/SuccessorQuotient.relation_aut_joint_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here BlockPermutationProduct is the dependent product, over quotient classes q, of the symmetric group on Fiber(R,q); centralizer(beta) is the centralizer of the singleton containing beta inside the symmetric group on Blocks(R). The image of the block action lies in this centralizer. Its kernel injects into the displayed product. Kernel times image gives the bound, retaining all block permutations.

## References

- Truth anchor: `D5/S3/FiniteGroups/SuccessorQuotient.assignmentEquiv`
- Truth anchor: `D5/S3/FiniteGroups/SuccessorQuotient.block_successor_commute`
- Truth anchor: `D5/S3/FiniteGroups/SuccessorQuotient.kernelRestriction`
- Truth anchor: `D5/S3/FiniteGroups/SuccessorQuotient.relation_aut_joint_bound`
