# Norm-Four Twisted Lowest Grades

## Abstract

The actual norm-four twisted zero mode on the ground and complete first half-oscillator grade.

Let D be finite-rank lattice data with an integral symmetric Gram matrix and even diagonal, and assume its determinant is a unit to obtain the chosen actual twisted ground. Write B for its bilinear form and U for the actual ground action of a charge a with B(a,a)=4. The ordinary lattice state is vector=(1/16)quadraticState+(s/4)chargedState. Its corrected twisted field is used throughout.

The half-mode normal-pair contraction has only the surviving indices -1 and 0 on a first oscillator, and vanishes on the ground. The finite quadratic correction contributes G(i,j)/8. For the charged coefficient, the translated first oscillator has support contained in {0,1}; its creation coefficients are 1 and 2P. These contractions give both action formulas.

**Definition 1.1 (The actual corrected zero mode).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.zeroMode`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.zeroMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary even integral symmetric lattice data D, a unit Gram determinant hu, a charge a and a complex scalar s, L is correctedField(D,hu,vector(D,a,s)).coeff(-4). The exponent is the native doubled exponent of the physical weight-two zero mode.

**Theorem 1.2 (Action on the actual twisted ground).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.zeroMode_ground`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.zeroMode_ground` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every charge a of squared norm four, every complex s and every u in the chosen actual ground, L(1 tensor u)=(1/32)(1 tensor u)+(s/32)(1 tensor Uu), where U is groundAction(D,hu,a). No condition on s squared is needed for this formula.

**Theorem 1.3 (Action on each first half oscillator).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.zeroMode_X`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.zeroMode_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every charge a of squared norm four, every complex s, every coordinate i and every actual ground vector u, put b_i=B(a,unitCharge(i)) and P=sum_j a_j X(j,0). Then L(X(i,0) tensor u)=((1/32)X(i,0)+(b_i/16)P) tensor u+(s/32)((X(i,0)-2b_i P) tensor Uu).

**Theorem 1.4 (The complete first half-oscillator grade).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.actualGrade_one_eq_span`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.actualGrade_one_eq_span` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D and hu, actualGrade(D,hu,1) equals the complex span of all X(i,0) tensor u, with i ranging over every coordinate and u over the entire chosen ground. This is the full eigenspace of the original actualTensorL0 with eigenvalue rank(D)/16+1/2. Every odd-weight-one monomial is a single variable at mode zero; the ambient tensor basis proves exhaustion.

**Definition 1.5 (Restriction to the complete actual grade).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.actualGradeOneZeroMode`

*Formalization.* `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.actualGradeOneZeroMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every norm-four a and every complex s, the computed action preserves the complete grade actualGrade(D,hu,1). Its restriction defines the endomorphism actualGradeOneZeroMode on that grade.

**Theorem 1.6 (Cubic of the actual restricted zero mode).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.actualGradeOneZeroMode_polynomial`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.actualGradeOneZeroMode_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every D, hu, norm-four a and complex s satisfying s squared equal to one, the actual restricted endomorphism satisfies L(L-(1/16)I)(L-(1/2)I)=0. Repeated application to X(i,0) tensor u uses U squared equal to the identity and the norm-four charge-direction contraction. The span equality extends the identity to the entire grade, including dependent or zero tensors.

These are algebraic statements for arbitrary even integral symmetric lattice data with the stated unit determinant and norm-four charge. Positivity, rootlessness, rank twenty-four, a chosen eigenbasis and an additional positive-rank premise are unnecessary. The construction is classical: Frenkel-Lepowsky-Meurman, Vertex Operator Algebras and the Monster; Dong-Nagatomo, arXiv:math/9808088, section 3.2; Bakalov-Kac, arXiv:math/0402315, section 4. The ordinary norm-four vector follows the formula cited by Shimakura, arXiv:1202.6107, equation (1.3).

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.actualGradeOneZeroMode`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.actualGradeOneZeroMode_polynomial`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.actualGrade_one_eq_span`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.zeroMode`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.zeroMode_X`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/NormFourLowestGrades.zeroMode_ground`
- Dependency: [D5/S3/VertexAlgebra/Lattice/NormFourVirasoroVector](../Lattice/NormFourVirasoroVector.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedMonodromy](../LatticeHalfFockChargedMonodromy.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCorrectedConformal](../LatticeHalfFockCorrectedConformal.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockGradedTrace](../LatticeHalfFockGradedTrace.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockGroundProducts](../LatticeHalfFockGroundProducts.md)
