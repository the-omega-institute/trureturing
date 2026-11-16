# Literal Two-Variable Frequency and Displacement Equations

## Abstract

Literal Two-Variable Frequency and Displacement Equations

The actual ordinary bilinear transpose transports the first-variable frequency certificate to the second variable.

**Definition 1.1 (firstModeDerivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.firstModeDerivative`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.firstModeDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either kernel and sign pair and complex u,v,z, this is u(1-u) times the first partial derivative plus delta(e,u) times the literal kernelMode, before subtracting the actual zero-row correction. Delta is (1-3u)/2 for the positive sign and -(u+1)/2 for the negative sign.

**Definition 1.2 (secondModeDerivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.secondModeDerivative`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.secondModeDerivative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For either kernel and sign pair and complex u,v,z, this is v(1-v) times the second partial derivative plus delta(f,v) times the literal kernelMode, before subtracting the actual zero-row correction.

**Theorem 1.3 (second_frequency).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.second_frequency`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.second_frequency` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every signed J/T kernel and every point in the joint normal-convergence disk, the second external frequency series equals the second-mode differential operator together with its actual opposite-sign zero-row correction.

**Theorem 1.4 (displacement_with_boundary).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.displacement_with_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.displacement_with_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all signed inputs and outputs and real 0<r<1, the original J sum of the two frequency actions and the original T difference of the two frequency actions equal the compiled source displacement products, while retaining the literal negative-zero row corrections.

**Theorem 1.5 (displacement_differential).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.displacement_differential`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.displacement_differential` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every sign pair and real 0<r<1, with norm(u)+sqrt(r)<1 and norm(v)+sqrt(r)<1, the original J satisfies modeScale(f,v) D_u J + modeScale(e,u) D_v J = (1-r) M_e(u) M_f(v) [a_e(u) h_f(v)+h_e(u) a_f(v)]/2 + modeB(e) modeB(f). The original full T satisfies the corresponding difference equation with a_e h_f-h_e a_f and no constant term. Here D_u and D_v are the two scaled frequency differential operators, M is the actual sourceMode, a is modeA, h is modeH with the original period logarithmic derivative, and the T identity contribution is retained.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.displacement_differential`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.displacement_with_boundary`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.firstModeDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.secondModeDerivative`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalEquations.second_frequency`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalFrequencyRows](OriginalGaussianExternalFrequencyRows.md)
