# Native Pair Kernel and Ordered Supports

## Abstract

The native pair-translation kernel has rectangular lower bounds and finite ordered diagonals.

For arbitrary lattice data D and two charges, pairTranslation replaces each oscillator creator X index by its constant lift minus the left pairing times X 0 ^ omega(index) minus the right pairing times X 1 ^ omega(index). pairConvolution evaluates the resulting finite bivariate polynomial against the two halfCreationCoeff sequences. Their composition is the complex-linear commonKernel, with two independent integer coefficient indices.

**Theorem 1.1 (Successive single translations give the pair translation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.pair_translation_composition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.pair_translation_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every oscillator polynomial, lifting the right halfTranslatedPolynomial through secondTranslationLift D left equals pairTranslation D left right. Polynomial induction checks constants, addition and the actual creator images.

**Theorem 1.2 (The constant kernel is the pair of creation coefficients).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_constant`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For scalar:C, commonKernel at first,second on C scalar equals C scalar * (halfCreationCoeff D left first * halfCreationCoeff D right second). The finite convolution monomial identity proves this consumed constant case.

**Theorem 1.3 (A creator produces both independent kernel shifts).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_creator`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_creator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On X index * p, the kernel equals X index times its value on p, minus the left pairing smul the value at first+omega(index),second, minus the right pairing smul the value at first,second+omega(index). Pair translation composition and the two bivariate convolution shifts supply the recurrence.

**Theorem 1.4 (Each polynomial has two integer lower support bounds).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_rectangular_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_rectangular_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every p there exist firstBound and secondBound such that first<firstBound or second<secondBound forces commonKernel(first,second,p)=0. The bounds are negatives of the coordinate maxima in the finite pair-translated polynomial support; negative half-creation indices vanish.

**Theorem 1.5 (Both ordered diagonals have finite support after application).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_ordered_finite_support`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_ordered_finite_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For fixed first,second,p, both natural-degree sequences with indices first+d,second-d and first-d,second+d have finite support. The decreasing coordinate eventually crosses its lower bound. OrderedProducts and ClearedKernel consume this statewise finiteness.

**Theorem 1.6 (Charge and coefficient-index exchange preserves the common kernel).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_branch_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_branch_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all first,second,p, commonKernel D left right first second p equals commonKernel D right left second first p. Polynomial induction uses the constant and creator identities; ClearedKernel consumes this equality when reflecting its finite coefficient range.

These repository-derived identities reuse the inherited half-creation, translation and finite convolution APIs. Rectangular lower support permits infinite bivariate support. The finite ordered sums are per polynomial, and no finite support in the endomorphism space, analytic convergence, actual ground action or full charged tensor locality is claimed by this module alone.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_branch_exchange`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_ordered_finite_support`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.common_kernel_rectangular_support`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_constant`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.kernel_creator`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockProductKernel.pair_translation_composition`
- Dependency: [D5/S3/VertexAlgebra/LatticeActualProductKernel](LatticeActualProductKernel.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockBivariateConvolution](LatticeHalfFockBivariateConvolution.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](LatticeHalfFockChargedTensorCoefficients.md)
