# Actual finite homogeneous Laurent carriers

## Abstract

Actual finite homogeneous Laurent carriers

**Theorem 1.1 (Actual finite homogeneous Laurent carriers).**

Lean statement: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/ActualLaurentCarriers.actual_finite_laurent_carriers`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/ActualLaurentCarriers.actual_finite_laurent_carriers` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Bojko Bakalov and Victor G. Kac (2004). *Twisted Modules over Lattice Vertex Algebras*. DOI: [10.1142/9789812702562_0001](https://doi.org/10.1142/9789812702562_0001). URL: <https://arxiv.org/abs/math/0402315v1>.

*Commentary.*

The actual current and two physical source slices have three independent locality orders. Their weighted common cleared array has finite homogeneous coefficient slices. For every actual input tensor, linear functional, signed lifts and signed total degree, a finite Laurent polynomial represents that slice in every ordered Hahn expansion.

The construction first supplies the actual common array and supported carriers. Homogeneous multiplication by each labelled difference shifts degree by one; division by the homogeneous clearing polynomial then identifies all ordered scalar coefficients. Negative degrees and zero slices are included. The resulting carriers supply the two actual local branches of the arbitrary-cutoff quotient theorem.

The general collision_absolute_evaluation theorem in CollisionAnalytic/AbsoluteEvaluation gives an absolute numerical evaluation of these original JAB homogeneous slices. Fix the supplied cutoff K, arbitrary signed lifts gamma and delta, actual input x, algebraic linear functional phi and signed numerator total t. Let L be the sum of the three independent threeOrders. The supplier's coefficient identity identifies every labelled integer Hahn coefficient of P/Q with phi of the actual ordered coefficient when the exponent total is t-L, and with zero otherwise. Thus, in every permutation sigma and at every nonzero coordinate tuple with strictly decreasing norms in that order, the complete integer-indexed family of these selected actual coefficients times the Laurent monomial z^e is absolutely summable and sums to P(z)/Q(z). Its absolute sum is bounded by the finite absolute Laurent numerator value times the product of inverse pole powers of abs(norm(z_i)-norm(z_j)); Q(z) is nonzero.

This application retains all source, input and functional quantifiers, negative Laurent exponents and signed totals. Its coordinates are those of threeFields: the current together with the two physical source slices, where physicalSlice with shift s selects raw coefficient 2*e-s at exponent e and raw coefficient -2*r-s-2 at mode r. It does not identify the raw twisted-field exponents with these coordinates or assert a branch-independent analytic substitution. The argument evaluates one fixed homogeneous slice; summing all t for an arbitrary algebraic-dual matrix coefficient still requires finite total-energy support or a genuine inter-slice growth estimate. No VOA, positivity, boundedness or Jacobi hypothesis is inserted.

Classical local-field provenance is Matsuo–Nagatomo and Bakalov–Kac (math/0402315). The source retains the mathlib Hahn/Laurent and partial-fraction authors and Scott Carnahan/vertexAlg composition attribution under Apache 2.0.

## References

- Truth anchor: `D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSliceQuotient/ActualLaurentCarriers.actual_finite_laurent_carriers`
- Dependency: [D5/S3/VertexAlgebra/ChargedResidue/Locality](../../ChargedResidue/Locality.md)
- Dependency: [D5/S3/VertexAlgebra/GroundRightCurrentTransport/NativeDefect](../../GroundRightCurrentTransport/NativeDefect.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedCollision/WeightedLocalCorrelator](../../LatticeHalfFockChargedCollision/WeightedLocalCorrelator.md)
- Dependency: [D5/S3/VertexAlgebra/NestedResidues/ContextualKernelExtraction](../ContextualKernelExtraction.md)
- Dependency: [D5/S3/VertexAlgebra/RationalCollision](../../RationalCollision.md)
