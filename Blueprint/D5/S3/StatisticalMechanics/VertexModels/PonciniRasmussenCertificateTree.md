# Shared certificate trees

## Abstract

Shared certificate trees

**Definition 1.1 (Tree).**

$$Tree: Type \to Type$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenCertificateTree.Tree` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.Tree is the shared inductive type. For α : Type its constructors are Tree.leaf : α → Tree α and Tree.node : Tree α → Tree α → Tree α. The diagram tables, incoming row table and Horner state trees use this type.

**Definition 1.2 (get).**

$$\forall A \in Type,\; \left(\forall a \in A,\; \forall j \in Nat,\; get\left(Tree.leaf\left(a\right), j\right) = a\right) \land \left(\forall l \in Tree\left(A\right),\; \forall r \in Tree\left(A\right),\; \forall j \in Nat,\; get\left(Tree.node\left(l, r\right), j\right) = ite\left(Nat.mod\left(j, 2\right) = 0, get\left(l, Nat.div\left(j, 2\right)\right), get\left(r, Nat.div\left(j, 2\right)\right)\right)\right)$$

*Formalization.* `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenCertificateTree.get` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree.get reads a natural index by parity and division by two. A denotes Lean's type parameter α. A leaf returns its value at every remaining index. The shared prb1_tree_data% elaborator preserves the expected type while disabling the information tree for literal data.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenCertificateTree.Tree`
- Truth anchor: `D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenCertificateTree.get`
