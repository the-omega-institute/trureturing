# Contraction of the Actual Free-Root Trace Energy

## Abstract

A real one-Lipschitz map contracts the original free-root trace energy on the fixed golden biased probability space.

**Definition 1.1 (potential).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.potential`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.potential` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For an arbitrary real root value c and original square-summable edge increments z, potential(c,z,p) is c plus the sum of z over all nonempty prefixes of the finite address p.

**Definition 1.2 (contractedCoordinate).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.contractedCoordinate`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.contractedCoordinate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On a nonempty edge p, the contracted coordinate is chi(potential(c,z,p)) minus chi(potential(c,z,dropLast(p))).

**Definition 1.3 (contracted).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.contracted`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.contracted` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a real one-Lipschitz chi, these original-edge coordinates form an element of the original edge ell2 space. Each coordinate has absolute value at most that of the corresponding original increment.

**Definition 1.4 (contractLp).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.contractLp`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.contractLp` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Composition by chi in the actual G=L2(Omega,M) is defined as the actual constant chi(0) plus composition by x mapped to chi(x)-chi(0). The shifted map vanishes at zero and is one-Lipschitz, so its L2 composition is defined. The probability measure is the original phi-biased product law M.

**Theorem 1.5 (Actual Trace Contraction).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.actual_trace_contraction`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.actual_trace_contraction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real one-Lipschitz map chi and every F in the original free-root trace domain D, contractLp(chi,F) equals chi composed with F almost everywhere for the actual measure M, belongs to D, and has original infimum energy at most energy(F). No condition chi(0)=0 is imposed.

Choose the attained least-energy extension F=constG(c)+Jz. Contract its value at every finite vertex and take differences along the original edges. The one-Lipschitz inequality bounds every new increment by its original increment, hence bounds the entire ell2 norm. Telescoping gives the contracted original potential at every finite vertex, including the freely transformed root chi(c).

The actual trace of the depth projection P_h z equals the finite prefix sum along each ray almost everywhere for M. The finite edge cutoffs are cofinal among finite subsets, so the square-summable single-edge expansion proves P_h z tends to z. Boundedness of the actual J and continuity of shifted Lipschitz composition pass the exact finite-depth telescoping identity to G. Thus the contracted trace is exactly constG(chi(c))+J(contracted increments). The attained-energy comparison then proves the energy inequality.

This establishes the normal-contraction property of the actual free-root form. It does not assert order preservation of the spectral heat semigroup. That conclusion additionally requires the associated resolvent minimizer, clipping comparison and the strong limit of resolvent powers, together with compatible polar and operator coordinates.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.actual_trace_contraction`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.contractLp`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.contracted`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.contractedCoordinate`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryMarkovSemigroup.potential`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm](BiasedBoundaryFreeRootForm.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceCovariance](FiniteSourceCovariance.md)
