# Word Nodes Are Reduced

## Abstract

Every left-right word carries a unimodular matrix, so every node of the tree is a fraction already in lowest terms.

The two generators of the tree are unimodular, and the matrix product preserves the unimodular equation. Every finite word of left and right steps therefore carries a unimodular matrix, and the lower row of a unimodular matrix is coprime. That is the tree's prototype primality statement: irreducibility is not checked node by node, it is inherited from the group.

The last conjunct is a non-collapse witness rather than a further property. Without it the universal statement would be satisfied by a map sending every word to one fixed matrix, which would make the quantifier decoration rather than content. Along an all-left word the lower-left coordinate equals the word length, so the quantifier ranges over infinitely many distinct nodes.

**Theorem 1.1 (Every tree word carries a reduced node).**

$$\forall w\in \operatorname{List} \operatorname{Bool},\ \operatorname{gcd}(M(w)_{d}, M(w)_{c}) = 1.$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.stern_brocot_nodes_are_reduced_package` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed conjunct is the coprimality of the lower row; the package also carries unimodularity, positivity of the lower-right coordinate, and the non-collapse witness.

## References

- Truth anchor: `D5/S3/PrimeForms/SternBrocot/WordNodesAreReduced.stern_brocot_nodes_are_reduced_package`
- Dependency: [D5/S3/PrimeForms/Crossing/ExactPropagation](../Crossing/ExactPropagation.md)
