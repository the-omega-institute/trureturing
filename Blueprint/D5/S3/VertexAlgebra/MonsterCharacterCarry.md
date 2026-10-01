# Rank-Three Character Carry

## Abstract

Exactly eight rank-three sign tables have alternating-bilinear corrections and a common determinant carry.

Let E be the three-dimensional vector space over F_2. A sign table f is zero on either zero argument, additive in its second argument, one on nonzero diagonal pairs, and has opposite values on distinct nonzero reversed pairs. The explicit cubic table f0 is fixed by its coordinate formula in the Lean source.

**Theorem 1.1 (Sign-table classification and determinant carry).**

Lean statement: `D5/S3/VertexAlgebra/MonsterCharacterCarry.classification_and_carry`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/MonsterCharacterCarry.classification_and_carry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Tathagata Basak (2017). *The octonions as a twisted group algebra*. URL: <https://arxiv.org/abs/1702.05705>.

*Commentary.*

Every table satisfying these finite equations is uniquely f0 plus an alternating bilinear form, and every such correction gives a table satisfying the equations. The three basis-pair values determine the correction, so there are exactly eight tables. For all g, h, k in E, the sum f(g,k) + f(h,k) + f(g+h,k) equals the determinant of the matrix with rows g, h, k. The determinant is additive in its first two arguments and zero on their diagonal; the carry satisfies the cocycle equation, and distinct nonzero first arguments admit a third argument with nonzero carry. The proof derives first-variable linearity of the correction from the opposite-pair equations and polarizes the cubic terms of f0. Basak's twisted-group-algebra table supplies historical context; this finite result does not construct a VOA, identify an actual fusion rule, or lift the sign table to an OPE.

## References

- Truth anchor: `D5/S3/VertexAlgebra/MonsterCharacterCarry.classification_and_carry`
