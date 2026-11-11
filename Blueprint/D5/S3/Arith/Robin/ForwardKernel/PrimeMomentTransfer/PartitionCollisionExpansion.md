# Partition collision expansion

## Abstract

Arbitrary-order quadratic moment expansion by equality partitions.

Let the index type be finite, let A be a commutative real algebra, and let ell be any real linear functional on A. Suppose Y(d)^2=a*Y(d)+b*1 for every index d. No normalization of ell, centering, independence, or positivity is required. All orders, including zero, and empty index types are allowed. A partition is represented by a Mathlib Setoid on the positions Fin k; its blocks are its quotient classes. Grouping tuples by their equality relation is the classical decomposition of a finite sum into fibers, also underlying the set-partition expansion of power sums; see Stanley, Enumerative Combinatorics, volume 1, second edition, section 3.1, for the partition lattice. The quadratic moment reduction is the algebraic consequence described below.

**Definition 1.1 (Quadratic remainder coefficients).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a and b define (u(0),v(0))=(0,1), and (u(m+1),v(m+1))=(a*u(m)+v(m),b*u(m)). These are the coefficients of the remainder of X^m modulo X^2-a*X-b.

**Theorem 1.2 (Reduction at every exponent).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a,b, every y in A satisfying y^2=a*y+b*1, and every natural m, y^m=u(m)*y+v(m)*1. Induction multiplies the preceding expression by y and uses the quadratic relation.

**Definition 1.3 (Realized equality patterns).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.tupleKernelPatterns`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.tupleKernelPatterns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural order k and finite index type, tupleKernelPatterns is the image of all maps d from Fin k to the index type under d mapped to Setoid.ker d. Partitions with more blocks than available indices are absent, since their contribution would be zero.

**Theorem 1.4 (Decomposition by equality pattern).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.sum_eq_tupleKernel_sums`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.sum_eq_tupleKernel_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, finite index type, additive commutative monoid M and function F from position tuples to M, the sum of F over all tuples equals the sum over realized kernel setoids sigma of the sum of F over tuples with kernel exactly sigma. This is Mathlib's finite fiber-sum theorem applied to Setoid.ker.

**Definition 1.5 (Block multiplicity).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelBlockSize`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelBlockSize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every k, setoid sigma on Fin k, and quotient class B, kernelBlockSize is the cardinality of the positions whose quotient class is B. Every quotient class has a representative, so each such block has positive size.

**Definition 1.6 (Residual distinct-block moment).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For ell, Y, coefficient functions f indexed by Fin k, a setoid sigma and a finite set S of its quotient blocks, kernelDistinctMoment sums, over tuples d with kernel exactly sigma, the product over positions i of f(i,d(i)) times ell of the product over B in S of Y(d(B.out)). The exact-kernel condition says that the tuple is constant on each block and that different blocks receive different indices. Thus the positional coefficient product is also the product of the block-aggregated coefficients. Every block-injective assignment corresponds to exactly one such tuple; representative choices do not change its values.

**Theorem 1.7 (The general collision expansion).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadratic_moment_eq_partition_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadratic_moment_eq_partition_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, ell, Y, a, b satisfying the quadratic relation and coefficient family f, quadraticFamilyMoment equals the sum over sigma in tupleKernelPatterns(k) and all finite subsets S of its quotient blocks of the product of u(size(B)) over B in S, times the product of v(size(B)) over B in the complement of S, times kernelDistinctMoment(ell,Y,f,sigma,S). The complement is within the finite quotient type. Group the positions by their kernel blocks, reduce each block power using the coefficient recurrence, expand the product of the resulting two-term sums, and apply linearity. The residual moment retains only distinct block values. This gives the quadratic collision reduction at every order.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelBlockSize`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs_pow`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadratic_moment_eq_partition_expansion`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.sum_eq_tupleKernel_sums`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.tupleKernelPatterns`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs](QuadraticMomentDefs.md)
