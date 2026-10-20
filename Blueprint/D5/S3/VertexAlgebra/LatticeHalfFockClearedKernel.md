# Finite Cleared Half-Fock Kernels

## Abstract

Doubled coefficient differences turn the supported native expansion into a finite exchange kernel.

For a fixed oscillator polynomial p, coefficientExpansion sums series.coeff(d) smul commonKernel(left,right,first+d,second-d,p) over natural d. The ordered-diagonal support theorem makes this sum finite even for an arbitrary power series. physicalDifference sends a distribution F to F(first-2,second)-F(first,second-2). All integer coefficient indices are retained.

**Theorem 1.1 (One physical difference multiplies the series by one minus the square).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.physical_difference_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.physical_difference_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying physicalDifference to coefficientExpansion(series,p) gives coefficientExpansion((1-t^2)*series,p) at first-2,second. The proof splits off degrees zero and one and reindexes the remaining finite tail by two.

**Theorem 1.2 (Iteration gives the exact doubled first-index shift).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.physical_difference_iterate`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.physical_difference_iterate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural order, the order-th power of physicalDifference gives coefficientExpansion((1-t^2)^order*series,p) at first-2*order,second. Induction preserves the signed integer shifts and the zero-order case.

**Theorem 1.3 (The native contraction clears at the absolute Gram order).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With N=natAbs(bilinear D left right), iteration applied to halfContraction gives the expansion of clearedPolynomial.toPowerSeries at first-2*N,second. This is a consumed composition of iteration and branch clearing.

**Theorem 1.4 (The cleared expansion has a finite polynomial coefficient range).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.cleared_polynomial_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.cleared_polynomial_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer gram, the expansion equals the sum over Finset.range(2*gram.natAbs+1), with coefficient clearedPolynomial(gram).coeff(d) and kernel indices first+d,second-d. Coefficients above the degree bound vanish.

**Theorem 1.5 (The cleared native expansions exchange their branches).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_exchange`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_exchange` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The N-fold physical difference of the left/right expansion at first,second equals that of the right/left expansion at second,first, for every oscillator polynomial. Finite range reflection, complementary coefficient reciprocity, common-kernel exchange and symmetry of the integral pairing prove it.

The result is repository-derived from the supported ProductKernel, BranchClearing and finite-sum interfaces. It is an oscillator coefficient identity; the actual tensor ground factors and their cocycle signs are supplied separately in PhysicalLocality. The finite cleared range does not assert finite support of the uncleared bivariate kernel or uniformly finite endomorphism-valued support.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.cleared_polynomial_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_exchange`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.native_cleared_kernel_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.physical_difference_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockClearedKernel.physical_difference_iterate`
- Dependency: [D5/S3/VertexAlgebra/BinomialKernelDelta](BinomialKernelDelta.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing](LatticeHalfFockBranchClearing.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockProductKernel](LatticeHalfFockProductKernel.md)
