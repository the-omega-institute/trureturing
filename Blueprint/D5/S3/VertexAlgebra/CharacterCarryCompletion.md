# Character carry in binary trees

## Abstract

A section character determines the record of every finite binary label tree.

Let E and C be commutative groups and let ell assign a character record to each coarse label. The carry of g and h is ell(g)+ell(h)-ell(g+h). A leaf has a coarse label and zero record; at a fork, the coarse labels add and the records add with their carry. No normalization of ell at zero is assumed.

**Theorem 1.1 (Every binary tree has the same expanded record formula).**

$$\forall T, \operatorname{evaluate}\left(T\right)=(\operatorname{total}\left(T\right), \operatorname{characterTotal}\left(T\right)-ell(\operatorname{total}\left(T\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CharacterCarryCompletion.tree_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction cancels both child section values against the carry at each fork. The resulting record is the sum of all leaf characters minus the character of the total coarse label, for every finite branching shape and parenthesization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/CharacterCarryCompletion.tree_expansion`
