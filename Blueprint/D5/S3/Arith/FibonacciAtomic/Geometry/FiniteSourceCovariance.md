# Finite Source Covariance Convergence

## Abstract

The uniformly weighted original finite sources have the original biased boundary mean and covariance as norm limits.

**Definition 1.1 (one).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.one`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.one` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, one(n) is the constant one in L2(mu(n)), where mu(n) gives every actual occurrence mass 1/N(n). Root, internal and terminal occurrences all participate.

**Definition 1.2 (v).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.v`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.v` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, v(n) is the adjoint of the original finite path map J(n), applied to one(n). It lies in the common real ell2 of nonempty Bool addresses.

**Definition 1.3 (B).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.B`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.B` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, B(n) is J(n)*J(n) on the common edge ell2. The node L2 codomain of J(n) depends on n.

**Definition 1.4 (Sigma).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.Sigma`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.Sigma` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural n, Sigma(n) is B(n) minus rankOne(v(n),v(n)). The rank-one map sends z to the inner product of v(n) with z, multiplied by v(n).

**Theorem 1.5 (Simultaneous Norm Limits).**

$$\forall epsilon: \mathbb{R}, ((0 < epsilon) \implies (\exists N: \mathbb{N}, (\forall n: \mathbb{N}, ((N \leq n) \implies ((\Vert (\operatorname{v}\left(n\right)) - (\operatorname{boundaryMean}\left(\right)) \Vert < epsilon) \land ((\Vert (\operatorname{B}\left(n\right)) - (\operatorname{comp}\left(\operatorname{adjoint}\left(\operatorname{boundaryTrace}\left(\right)\right), \operatorname{boundaryTrace}\left(\right)\right)) \Vert < epsilon) \land (\Vert (\operatorname{Sigma}\left(n\right)) - (\operatorname{boundarySigma}\left(\right)) \Vert < epsilon)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.finite_source_covariance_convergence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the formula, boundaryMean is BiasedBoundaryFreeRootForm.v, boundaryTrace is BiasedBoundaryTrace.J, and boundarySigma is BiasedBoundaryFreeRootForm.Sigma. For every positive real epsilon there is one natural N such that every n at least N satisfies all three norm bounds. The finite objects use the original all-occurrence law and the original cardinality N(n). The boundary objects are precisely those of BiasedBoundaryTrace and BiasedBoundaryFreeRootForm, with a equal to the inverse golden ratio and b equal to its inverse square. False is L and true is R.

The original path maps ignore absent edges and vanish at the root. The definitions include the singleton sources n=0 and n=1. The claim compares the mean vectors and operators on the common edge Hilbert space; it requires no identification of the changing node spaces.

The exact node cardinality and Fibonacci formula give convergence of every fixed descendant mass. Comparable addresses have Gram entry equal to the mass of the longer address; incomparable addresses have entry zero. These identities hold for absent addresses as well.

For a fixed depth h the coordinate projection has finite support. Its mean block is the sum of descendant masses times unit edge vectors, and its Gram block is the double sum of Gram coefficients times coordinate rank-one maps. The finite blocks therefore converge in norm.

The Hardy remainders are dK(h)=sqrt(2*goldenRatio*a^(h+1)/(1-a)) and dOne(h)=sqrt(a^(h+1)/(1-a)). The mean error is at most dK(h)+dOne(h) plus the finite mean-block error. The Gram error is at most 2*dK(0)*dK(h)+2*dOne(0)*dOne(h) plus the finite Gram-block error. Choose h first and then the common source threshold. Continuity of rankOne gives the centered covariance limit.

This result states the three norm limits. It supplies no finite counting-screening resolvent identity.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.B`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.Sigma`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.finite_source_covariance_convergence`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.one`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance.v`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm](BiasedBoundaryFreeRootForm.md)
