# Character carry and recorded composition

## Abstract

A section character determines an associative recorded law and the record of every finite fusion tree.

Let E and C be commutative groups and let ell assign a character record to each coarse label. The carry of g and h is ell(g)+ell(h)-ell(g+h). A recorded pair (g,c) expands to (g,c+ell(g)); its composition has coarse component g+h and record c+d+carry(g,h). When ell(0)=0, the zero recorded pair is the identity. The binary-tree formula needs no normalization of ell.

**Theorem 1.1 (The recorded law is uniquely determined by expansion).**

$$ell(0)=0\Rightarrow(\ (\forall x, y, \operatorname{Expand}\left(\operatorname{compose}\left(x, y\right)\right)=\operatorname{Expand}\left(x\right)+\operatorname{Expand}\left(y\right)) \land\ \operatorname{Bijective}\left(Expand\right) \land\ (\forall x, y, z, \operatorname{compose}\left(\operatorname{compose}\left(x, y\right), z\right)=\operatorname{compose}\left(x, \operatorname{compose}\left(y, z\right)\right)) \land\ (\forall x, \operatorname{compose}\left(0, x\right)=x=\operatorname{compose}\left(x, 0\right)) \land\ (\forall x, y, \operatorname{compose}\left(x, y\right)=\operatorname{compose}\left(y, x\right)) \land\ (\forall x, \exists y, \operatorname{compose}\left(x, y\right)=0 \land \operatorname{compose}\left(y, x\right)=0) \land\ (\forall op, (\forall x, y, \operatorname{Expand}\left(\operatorname{op}\left(x, y\right)\right)=\operatorname{Expand}\left(x\right)+\operatorname{Expand}\left(y\right)) \Rightarrow \forall x, y, \operatorname{op}\left(x, y\right)=\operatorname{compose}\left(x, y\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CharacterCarryCompletion.recorded_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expansion is injective because each character fiber is translated by a fixed value. The carry cancels the section discrepancy, so expanded composition is ordinary addition. The inverse fiber translation makes expansion bijective. It transfers associativity, commutativity, identity, and inverses back to recorded pairs, and forces any other operation with the same expansion law to agree.

The correction is a coboundary of the chosen section. The result does not assert a nontrivial extension class or construct a fusion category.

**Theorem 1.2 (Every binary tree has the same expanded record formula).**

$$\forall T, \operatorname{evaluate}\left(T\right)=(\operatorname{total}\left(T\right), \operatorname{characterTotal}\left(T\right)-ell(\operatorname{total}\left(T\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/CharacterCarryCompletion.tree_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A leaf carries a coarse label and zero extra record. At each binary node the two recorded values compose. Induction cancels both child section values against the new carry, leaving the sum of all leaf characters minus the character of the total coarse label. The formula holds for every finite branching shape and parenthesization.

## References

- Truth anchor: `D5/S3/VertexAlgebra/CharacterCarryCompletion.recorded_composition`
- Truth anchor: `D5/S3/VertexAlgebra/CharacterCarryCompletion.tree_expansion`
