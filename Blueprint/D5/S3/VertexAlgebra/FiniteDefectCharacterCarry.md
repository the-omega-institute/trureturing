# Finite defect character carry

## Abstract

The eight rank-three sign tables have the same character carry.

**Theorem 1.1 (All alternating choices give one carry).**

$$\forall m, g, h\in E,\ \operatorname{carry}\left(\operatorname{ell}\left(m\right), g, h\right)=\operatorname{wedge}\left(g, h\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FiniteDefectCharacterCarry.carry_is_wedge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three coordinates of m choose an alternating bilinear correction to the explicit sign table f0. The value ell_m(g) is the sign on the three coordinate basis vectors, so it records the character of the second input. In the carry ell_m(g)+ell_m(h)-ell_m(g+h), every alternating correction cancels. The remaining three coordinates are the pairwise minors of g and h.

Pairing this wedge with a third label gives the characteristic-two determinant. The identity concerns the finite sign system; it does not assert existence of a vertex operator algebra or its module category.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FiniteDefectCharacterCarry.carry_is_wedge`
- Dependency: [D5/S3/VertexAlgebra/CharacterCarryCompletion](CharacterCarryCompletion.md)
