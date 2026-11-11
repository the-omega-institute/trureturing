# Partition collision expansion

## Abstract

Arbitrary-order quadratic moment expansion by equality partitions.

Let the index type be finite, let A be a commutative real algebra, and let ell be any real linear functional on A. Suppose Y(d)^2=a*Y(d)+b*1 for every index d. No normalization of ell, centering, independence, or positivity is required. All orders, including zero, and empty index types are allowed. A partition is represented by a Mathlib Setoid on the positions Fin k; its blocks are its quotient classes. Grouping tuples by their equality relation is the classical decomposition of a finite sum into fibers, also underlying the set-partition expansion of power sums; see Stanley, Enumerative Combinatorics, volume 1, second edition, section 3.1, for the partition lattice. The quadratic moment reduction extends the finite collision identities of Lemma 498.2 in FIBONACCI_ANALYTIC_FRONTIER_INTERFACES_II.

**Definition 1.1 (Quadratic remainder coefficients).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For real a and b let u(m) and v(m) be the imaginary and real coordinates of omega^m in Mathlib QuadraticAlgebra with omega^2=b+a*omega. These are the coefficients of the remainder of X^m modulo X^2-a*X-b.

**Theorem 1.2 (Reduction at every exponent).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs_pow`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs_pow` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real a,b, every y in A satisfying y^2=a*y+b*1, and every natural m, y^m=u(m)*y+v(m)*1. The universal algebra homomorphism evaluating omega at y preserves powers.

**Theorem 1.3 (Degree-sensitive coefficient bound).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real a,b,C,L with C>=1, L>=1, |a|<=C*L and |b|<=C*L, and every natural m>=1, both |u(m)| and |v(m)| are at most ((C+1)*L)^(m-1). The coordinate recurrence of multiplication by omega gives u(m+1)=a*u(m)+v(m) and v(m+1)=b*u(m). The inequality C*L+1<=(C+1)*L propagates the bound.

**Definition 1.4 (Realized equality patterns).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.tupleKernelPatterns`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.tupleKernelPatterns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a natural order k and finite index type, tupleKernelPatterns is the image of all maps d from Fin k to the index type under d mapped to Setoid.ker d. Partitions with more blocks than available indices are absent, since their contribution would be zero.

**Theorem 1.5 (Decomposition by equality pattern).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.sum_eq_tupleKernel_sums`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.sum_eq_tupleKernel_sums` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k, finite index type, additive commutative monoid M and function F from position tuples to M, the sum of F over all tuples equals the sum over realized kernel setoids sigma of the sum of F over tuples with kernel exactly sigma. This is Mathlib's finite fiber-sum theorem applied to Setoid.ker.

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

For every k, ell, Y, a, b satisfying the quadratic relation and coefficient family f, quadraticFamilyMoment equals the sum over sigma in tupleKernelPatterns(k) and all finite subsets S of its quotient blocks of the product of u(size(B)) over B in S, times the product of v(size(B)) over B in the complement of S, times kernelDistinctMoment(ell,Y,f,sigma,S). The complement is within the finite quotient type. Group the positions by their kernel blocks, reduce each block power using quadratic-algebra evaluation, expand the product of the resulting two-term sums, and apply linearity. The residual moment uses distinct indices for the retained blocks. This gives the quadratic collision reduction at every order.

**Theorem 1.8 (Blocks have positive size).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quotient_mult_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quotient_mult_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every quotient block of a setoid on Fin k has multiplicity at least one, witnessed by its chosen representative.

**Theorem 1.9 (All block sizes sum to k).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.sum_quotient_multiplicities`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.sum_quotient_multiplicities` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every setoid sigma on Fin k, the sum of the multiplicities of its quotient classes is k. These multiplicities are the cardinalities of the fibers of the quotient map, which partition Fin k.

**Theorem 1.10 (Coefficient bound for one retained set).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.partition_coefficient_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.partition_coefficient_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For C,L>=1 and |a|,|b|<=C*L, the product of u(size(B)) over retained blocks and v(size(B)) over the others has absolute value at most ((C+1)*L)^(k-card(Quotient sigma)).

**Theorem 1.11 (Block-injective assignment formula).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_eq_block_assignments`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_eq_block_assignments` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual kernel moment equals the sum over injective assignments from Quotient sigma to the index type, with positional weight product evaluated through the quotient map and the product of Y over retained blocks.

**Theorem 1.12 (Edge expansion with aggregated block weights).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_eq_collision_assignment_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_eq_collision_assignment_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The residual kernel moment equals the signed edge-subset sum of collisionAssignmentMoment with weights aggregated over the original partition blocks.

**Theorem 1.13 (The empty-edge main term).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionAssignmentMoment_empty`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionAssignmentMoment_empty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary block weights and retained set S, the collision assignment moment with no edges equals the product of free weight sums times distinctIndexMoment of the retained weights, enumerated by equivFin(S).

**Definition 1.14 (Collision tests away from retained pairs).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionEdges`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite block type B and retained set S, collisionEdges(S) consists of ordered pairs of distinct blocks with at least one endpoint outside S. Both orientations are included. Their repeated equality tests have the same zero-one product as a single test per unordered pair. There are at most card(B)^2 tests, so at most 2^(card(B)^2) edge subsets.

**Theorem 1.15 (Edge-subset inclusion-exclusion).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_eq_edge_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_eq_edge_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every order k, ell, Y, coefficient family f, partition sigma and retained block set S, the residual kernel moment equals the sum over subsets G of collisionEdges(S), with sign (-1)^card(G), of the sum over block assignments phi that are injective on S and equal on every edge of G. Each summand has the original positional weight product times ell of the product of Y(phi(B)) over retained blocks. Block-injective assignments correspond bijectively to positional tuples whose kernel is exactly sigma. Expand the product of one minus each equality indicator, keeping the retained injectivity indicator outside that product.

**Definition 1.16 (Connected collision components).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionComponents`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionComponents` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite edge set G on any type B, collisionComponents(G) is the setoid generated by its directed edges. Its equivalence classes are the connected components after forgetting edge orientation.

**Definition 1.17 (Moment with prescribed collision edges).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionAssignmentMoment`

*Formalization.* `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionAssignmentMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite block type, block weights w, retained set S and edge set G, sum over assignments injective on S and equal at every edge of G. The summand is the full block weight product times ell of the retained Y product.

**Theorem 1.18 (Quantitative removal of block collisions).**

Lean statement: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_collision_estimates`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_collision_estimates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume C>=1, H>=1, s>=0, ell(1)=1, ell(Y(d))=0, card(D)<=C*H and |f(i,d)|<=1. Assume DisjointLabelMomentBound(ell,Y,f,C,s), and let sigma have t blocks with retained set S of size r<k and complement size q. Then |kernelDistinctMoment| <= 2^(t*t)*C^(q+1)*H^q*s^r. For q>=1, subtracting the collision-free main term, namely the product of free block scalar sums times the distinct moment of the retained block weights, leaves absolute error at most 2^(t*t)*C^q*H^(q-1)*s^r. Each edge subset has at most q free components, and a nonempty subset has at most q-1 because every allowed edge joins distinct blocks and touches a free block. The total number of subsets is at most 2^(t*t). Signed cancellation inside each retained distinct-index moment is preserved.

## References

- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionAssignmentMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionAssignmentMoment_empty`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionComponents`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.collisionEdges`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_collision_estimates`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_eq_block_assignments`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_eq_collision_assignment_sum`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.kernelDistinctMoment_eq_edge_expansion`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.partition_coefficient_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs_bound`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadraticPowerCoeffs_pow`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quadratic_moment_eq_partition_expansion`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.quotient_mult_pos`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.sum_eq_tupleKernel_sums`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.sum_quotient_multiplicities`
- Truth anchor: `D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartitionCollisionExpansion.tupleKernelPatterns`
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/ArithmeticTransferDefs](ArithmeticTransferDefs.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/CollisionComponentFactor](CollisionComponentFactor.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/MergedLabelMomentBounds](MergedLabelMomentBounds.md)
- Dependency: [D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/QuadraticMomentDefs](QuadraticMomentDefs.md)
