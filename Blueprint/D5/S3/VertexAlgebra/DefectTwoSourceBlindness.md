# Two-source determinant blindness

## Abstract

Two defect directions have zero cubic carry response on their entire span.

**Theorem 1.1 (Two sources cannot detect the cubic carry).**

$$\forall m, g, h\in E, a, b, c, d, e, f\in F_2,\ \operatorname{dot}\left(\operatorname{carry}\left(\operatorname{ell}\left(m\right), \operatorname{plane}\left(g, h, a, b\right), \operatorname{plane}\left(g, h, c, d\right)\right), \operatorname{plane}\left(g, h, e, f\right)\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/DefectTwoSourceBlindness.two_source_carry_blind` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every plane expression is a linear combination of the same two defect labels g and h. The carry of two such expressions is their wedge product, and pairing it with any third expression from that plane is zero. Thus arbitrary binary composition of labels from two fixed sources remains unable to produce a negative cubic determinant sign. An independent third label is required to observe it.

## References

- Truth anchor: `D5/S3/VertexAlgebra/DefectTwoSourceBlindness.two_source_carry_blind`
- Dependency: [D5/S3/VertexAlgebra/FiniteDefectCharacterCarry](FiniteDefectCharacterCarry.md)
