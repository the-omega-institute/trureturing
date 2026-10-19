# Radial convexity and endpoint derivatives

## Abstract

Endpoint derivative pairings imply both Frobenius distance inequalities on ordered matrix intervals.

**Definition 1.1 (Hermitian functional calculus).**

Lean statement: `D5/S3/Quantum/Matrix/RadialConvexity.matFun`

*Formalization.* `D5/S3/Quantum/Matrix/RadialConvexity.matFun` (`✓ std3`).

*Citation.* M. M. Czerwińska; J. A. Franco; A. Merino (2026). *Towards a Characterization of Matrix Monotonicity via Radial Convexity*. DOI: [10.48550/arXiv.2610.17393](https://doi.org/10.48550/arXiv.2610.17393). URL: <https://arxiv.org/abs/2610.17393>.

*Commentary.*

The real scalar function is applied by continuous functional calculus to a complex Hermitian matrix. The predicates use positive definite matrices, whose entire spectrum lies in the function's domain (0,∞).

**Definition 1.2 (The Frobenius norm).**

Lean statement: `D5/S3/Quantum/Matrix/RadialConvexity.frobeniusNorm`

*Formalization.* `D5/S3/Quantum/Matrix/RadialConvexity.frobeniusNorm` (`✓ std3`).

*Citation.* M. M. Czerwińska; J. A. Franco; A. Merino (2026). *Towards a Characterization of Matrix Monotonicity via Radial Convexity*. DOI: [10.48550/arXiv.2610.17393](https://doi.org/10.48550/arXiv.2610.17393). URL: <https://arxiv.org/abs/2610.17393>.

*Commentary.*

The Euclidean norm of the vector of all complex matrix entries is the Frobenius norm: its square is the sum of squared entry moduli. The definition reuses CartesianVariance.vectorize and its norm-square identity. It does not change the norm instance used by continuous functional calculus.

**Definition 1.3 (Radial convexity of order n).**

Lean statement: `D5/S3/Quantum/Matrix/RadialConvexity.RadiallyConvexOrder`

*Formalization.* `D5/S3/Quantum/Matrix/RadialConvexity.RadiallyConvexOrder` (`✓ std3`).

*Citation.* M. M. Czerwińska; J. A. Franco; A. Merino (2026). *Towards a Characterization of Matrix Monotonicity via Radial Convexity*. DOI: [10.48550/arXiv.2610.17393](https://doi.org/10.48550/arXiv.2610.17393). URL: <https://arxiv.org/abs/2610.17393>.

*Commentary.*

For every positive definite complex n×n triple A≤C≤B, both ‖f(C)−f(A)‖F and ‖f(B)−f(C)‖F are at most ‖f(B)−f(A)‖F. The Loewner order is Mathlib's MatrixOrder: A≤B means B−A is positive semidefinite.

**Definition 1.4 (Matrix monotonicity of degree n).**

Lean statement: `D5/S3/Quantum/Matrix/RadialConvexity.MatrixMonotoneDegree`

*Formalization.* `D5/S3/Quantum/Matrix/RadialConvexity.MatrixMonotoneDegree` (`✓ std3`).

*Citation.* M. M. Czerwińska; J. A. Franco; A. Merino (2026). *Towards a Characterization of Matrix Monotonicity via Radial Convexity*. DOI: [10.48550/arXiv.2610.17393](https://doi.org/10.48550/arXiv.2610.17393). URL: <https://arxiv.org/abs/2610.17393>.

*Commentary.*

On all positive definite complex n×n matrices, the functional calculus either preserves every Loewner comparison or reverses every Loewner comparison. This includes both directions allowed by Definition 2.15 of the source.

**Definition 1.5 (The endpoint positivity property).**

Lean statement: `D5/S3/Quantum/Matrix/RadialConvexity.EndpointDerivativePositive`

*Formalization.* `D5/S3/Quantum/Matrix/RadialConvexity.EndpointDerivativePositive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every ordered pair U≤V in the domain and every positive direction K, both endpoint pairings ⟨g(V)−g(U),D(U)K⟩ and ⟨g(V)−g(U),D(V)K⟩ are nonnegative.

**Theorem 1.6 (Endpoint derivative criterion).**

Lean statement: `D5/S3/Quantum/Matrix/RadialConvexity.radial_inequalities_of_endpoint_derivative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/RadialConvexity.radial_inequalities_of_endpoint_derivative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g map an ordered real normed space into a real Hilbert space. Suppose ordered segments remain in the domain, g has derivative D at every domain point, and both endpoint inner products ⟨g(V)−g(U),D(U)K⟩ and ⟨g(V)−g(U),D(V)K⟩ are nonnegative whenever U≤V and K≥0. Then g satisfies both radial norm inequalities on every ordered triple A≤C≤B in the domain.

Along C+t(B−C), the squared distance from g(A) has nonnegative derivative. Along A+t(C−A), the squared distance from g(B) has nonpositive derivative. The real mean value theorem gives both comparisons, and nonnegativity of norms removes the squares. This criterion separates the calculus argument from the matrix-specific proof of endpoint positivity.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/RadialConvexity.EndpointDerivativePositive`
- Truth anchor: `D5/S3/Quantum/Matrix/RadialConvexity.MatrixMonotoneDegree`
- Truth anchor: `D5/S3/Quantum/Matrix/RadialConvexity.RadiallyConvexOrder`
- Truth anchor: `D5/S3/Quantum/Matrix/RadialConvexity.frobeniusNorm`
- Truth anchor: `D5/S3/Quantum/Matrix/RadialConvexity.matFun`
- Truth anchor: `D5/S3/Quantum/Matrix/RadialConvexity.radial_inequalities_of_endpoint_derivative`
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](CartesianVariance.md)
