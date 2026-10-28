# The Biased Boundary Trace

## Abstract

Cylinder path sums extend from finite increments to the common real edge ell2 on the fixed golden biased boundary.

**Definition 1.1 (b).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.b`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.b` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The right-child mass b is the square of the reciprocal golden ratio a. Their sum is one.

**Definition 1.2 (Omega).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.Omega`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.Omega` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A ray is a function from the natural numbers to Bool. The value false is the left branch and true is the right branch.

**Definition 1.3 (bit).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.bit`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.bit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The letter law gives mass a to false and mass b to true.

**Definition 1.4 (M).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.M`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.M` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M is the infinite product of this same letter law at every coordinate.

**Definition 1.5 (G).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.G`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.G` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G is real L2 for M. Every finite path sum and its limit belong to this fixed space.

**Definition 1.6 (cylinder).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.cylinder`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.cylinder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cylinder of p prescribes precisely its original initial address coordinates. The empty cylinder is the entire ray space.

**Definition 1.7 (mass).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.mass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The cylinder mass is the product of the biased letter probabilities along its finite address.

**Definition 1.8 (indicator).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.indicator`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.indicator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A unit increment at a nonempty address is the L2 indicator of its cylinder.

**Definition 1.9 (J).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.J`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

J is the continuous linear extension of the actual cylinder indicator sum on finitely supported increments. Its domain is the original real edge ell2 H.

**Theorem 1.10 (Positive Left Probability).**

$$0< a$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.a_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reciprocal golden ratio a is strictly positive because the golden ratio is positive.

**Theorem 1.11 (Strict Contraction of Mass).**

$$a< 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.a_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The left probability a is strictly smaller than one because the golden ratio exceeds one. Hence powers of a decay to zero, giving a common finite depth for every positive mass threshold.

**Theorem 1.12 (Conservation of Probability).**

$$a+b=1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.sum_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The golden conjugate equation gives a plus its square equal to one. Thus the two child probabilities a and b sum to one at every vertex.

**Theorem 1.13 (Actual Cylinder Mass).**

$$\forall p: \operatorname{Address}\left(\right), (\operatorname{toReal}\left(\operatorname{M}\left(\operatorname{cylinder}\left(p\right)\right)\right)=\operatorname{mass}\left(p\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.cylinder_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original finite address p, including the empty address, the real mass of its cylinder under the infinite Bernoulli product M is exactly the product of its letter probabilities: a for false and b for true.

The finite-coordinate product formula for M reduces the cylinder measure to singleton probabilities. Appending one letter multiplies both that measure and mass(p) by the same probability. The empty address has mass one. Consequently this is the actual cylinder mass used by the mass-crossing frontier.

**Theorem 1.14 (An Actual Single Increment).**

$$\forall p: \operatorname{Edge}\left(\right), (\forall c: \mathbb{R}, (\operatorname{J}\left(\operatorname{single}\left(2, p, c\right)\right)=(c) \cdot (\operatorname{indicator}\left(p\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.J_single` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original nonempty edge p and real increment c, J sends the square-summable single-coordinate vector to c times the actual biased cylinder indicator. This identifies the coordinate covariance with the intersection probabilities of the same measure M.

**Theorem 1.15 (Convergence and Hardy Tail).**

$$(\forall z: \operatorname{H}\left(\right), (\operatorname{HasSum}\left((p: \operatorname{Edge}\left(\right) \mapsto (\operatorname{coordinate}\left(z, p\right)) \cdot (\operatorname{indicator}\left(p\right))), \operatorname{J}\left(z\right)\right)))\land(\forall h: \mathbb{N}, (\forall z: \operatorname{H}\left(\right), ((\Vert \operatorname{J}\left((z) - (\operatorname{P}\left(h, z\right))\right) \Vert)^{2}\leq(\frac{(a)^{h+1}}{(1) - (a)}) \cdot ((\Vert z \Vert)^{2}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.boundary_trace_hardy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every square-summable real increment vector, the sum of its weighted cylinder indicators converges in L2 to Jz. The sum is over all nonempty original addresses, and convergence is along finite subsets.

For every natural depth h, including zero, removing the coordinates of length at most h leaves a trace with squared norm at most a to the power h+1 divided by 1-a times the original squared edge norm.

A ray has at most one prefix of each length. Weighted Cauchy-Schwarz and the geometric sum bound its finite path sum. Integrating each cylinder term introduces its actual biased mass, bounded above by a to the address length. This cancels the reciprocal weight and leaves the real ell2 energy.

The finite-increment inclusion has dense range in H. The uniform finite-sum estimate extends the path map continuously, and the canonical single-coordinate expansion in ell2 gives its L2 sum formula. Passing the finite Hardy estimate to this limit proves the all-vector tail.

The conditional suffix identity, the stopping-cylinder projection and its residual estimate require additional results. No spectral counting, compact resolvent or free-root form identification follows from this statement alone.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.G`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.J`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.J_single`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.M`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.Omega`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.a_lt_one`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.a_pos`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.b`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.bit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.boundary_trace_hardy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.cylinder`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.cylinder_mass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.indicator`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.mass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace.sum_weights`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy](FiniteSourceHardy.md)
