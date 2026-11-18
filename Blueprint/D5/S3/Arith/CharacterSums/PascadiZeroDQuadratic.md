# Zero Dixon residual and quadratic pencils

## Abstract

The actual Dixon determinant of three LQ coefficient rows supplies the missing constant-baseline quadratic elimination. Together with the common-direction cofactor estimate, it gives a sixth-height resultant theorem even when the baseline leading pair vanishes.

**Theorem 1.1 (The constant-baseline Dixon identity).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiZeroDQuadratic.constant_base_dixon_quadratic_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiZeroDQuadratic.constant_base_dixon_quadratic_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Over any commutative ring, take three rows (qi,ri,si,li,mi), with Li=li+mi*T, Qi=qi+ri*T+si*T², and Pi=L0*Qi-Li*Q0. If m0=s0=0, the existing three-column-minor Dixon residual D satisfies l0*D=−(m1*s2−m2*s1)*Res22(P1,P2). The residual is exactly PrimeCube.residual, rather than a newly chosen eliminant. Expanding the fixed quadratic resultant formula and the Dixon determinant proves the identity without cancellation, nonzero coefficients or characteristic restrictions.

**Theorem 1.2 (Sixth-height elimination including a zero leading baseline).**

Lean statement: `D5/S3/Arith/CharacterSums/PascadiZeroDQuadratic.zero_dixon_quadratic_resultant_zero`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/PascadiZeroDQuadratic.zero_dixon_quadratic_resultant_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let p be prime, b an integer, I,J≥1, and assume the literal bounds |li|≤3I, |mi|≤3J, |qi|≤I², |ri|≤2IJ, |si|≤J². Suppose P1,P2 have degree exactly two, P1 has nonzero reduction modulo p, both values at b are divisible by p³, both derivatives there by p, L0(b) is a unit modulo p, and the actual Dixon residual is zero. Then 6804*I⁶*J⁴<p⁵ implies Res22(P1,P2)=0. A nonzero reduction for P2 is unnecessary for this elimination theorem.

Vanishing cubic coefficients force collinearity with the baseline leading pair. If that pair is nonzero, a primitive direction and its weighted bounds feed directly into quadratic_direction_resultant_zero. If m0=s0=0 and the partner minor is nonzero, the displayed Dixon identity forces the resultant to vanish without a height comparison. If the partner minor is zero, the first genuine quadratic has a nonzero partner leading pair; reindexing the primitive-direction selection at that partner gives the same weighted direction estimate. The existing cofactor theorem permits k0=0, so this final case uses precisely the same sixth-height gap. No rank assumption, baseline resultant unit, or seventh-height estimate is used.

The new identity and its degeneracy split implement an algebraic step in the prime-cube approach to Pascadi's count. They do not establish a new total counting exponent, the arbitrary-modulus conjecture, or literature priority.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiZeroDQuadratic.constant_base_dixon_quadratic_identity`
- Truth anchor: `D5/S3/Arith/CharacterSums/PascadiZeroDQuadratic.zero_dixon_quadratic_resultant_zero`
- Dependency: [D5/S3/Arith/CharacterSums/PascadiQuadraticDirection](PascadiQuadraticDirection.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiQuadraticPrimitiveDirection](PascadiQuadraticPrimitiveDirection.md)
- Dependency: [D5/S3/Arith/CharacterSums/PascadiSeventhHeightCover](PascadiSeventhHeightCover.md)
