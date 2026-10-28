# Actual Cylinder Averages

## Abstract

Actual normalized cylinder integrals define a finite average operator on the original biased boundary Hilbert space. Prefix freedom makes it the orthogonal projection onto the cylinder span.

**Definition 1.1 (atomMean).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.atomMean`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.atomMean` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a nonempty original address p, atomMean(p) is the inner product with the actual cylinder indicator, divided by the actual M mass of that cylinder. It is a continuous real functional on the original L2(M).

**Definition 1.2 (Q).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.Q`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite set A of original nonempty addresses, Q(A) is the sum over p in A of the actual cylinder indicator multiplied by atomMean(p). The operator is constructed as a finite sum of continuous linear maps.

**Definition 1.3 (V).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.V`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.V` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V(A) is the real linear span in the original L2(M) of the actual indicators of the cylinders with addresses in A.

**Definition 1.4 (V0).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.V0`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.V0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

V0(A) is the kernel of the actual mean restricted to V(A). Its elements are exactly the vectors in the actual cylinder span whose original M mean is zero.

**Theorem 1.5 (Original Cylinders and Ray Prefixes).**

$$\forall p: \operatorname{Address}\left(\right), (\forall omega: \operatorname{Omega}\left(\right), (\operatorname{InCylinder}\left(omega, p\right)\iff p=\operatorname{rayPrefix}\left(omega, \operatorname{length}\left(p\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.cylinder_ray` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original address p and ray omega, omega lies in the actual cylinder of p precisely when p is the prefix of omega of length length(p). This includes the empty address. The cylinder prescribes the same initial coordinates as the list constructed by rayPrefix, so equality follows by comparing every list entry.

This correspondence converts a unique prefix on each ray into a unique actual cylinder containing that ray. In particular it identifies the product-tree mass frontier with a covering of the original Bernoulli boundary.

**Theorem 1.6 (Normalized Means and Orthogonal Projection).**

$$\forall A: \operatorname{Finset}\left(\operatorname{Edge}\left(\right)\right), (\operatorname{IsPrefixFree}\left(\operatorname{addresses}\left(A\right)\right)\implies (\forall p: \operatorname{Edge}\left(\right), (\forall F: \operatorname{G}\left(\right), (\operatorname{atomMean}\left(p, F\right)=\operatorname{normalizedSetIntegral}\left(M, \operatorname{cylinder}\left(\operatorname{val}\left(p\right)\right), F\right))))\land (\forall p: \operatorname{Edge}\left(\right), (\forall F: \operatorname{G}\left(\right), (\operatorname{atomMean}\left(p, F\right)=\operatorname{mean}\left(\operatorname{pullback}\left(\operatorname{val}\left(p\right), F\right)\right))))\land (\forall F: \operatorname{G}\left(\right), (\operatorname{Q}\left(A, F\right)=\operatorname{starProjection}\left(\operatorname{V}\left(A\right), F\right)))\land (\forall p\in A, \operatorname{Q}\left(A, \operatorname{indicator}\left(p\right)\right)=\operatorname{indicator}\left(p\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.cylinder_average_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite A whose original addresses are prefix-free, atomMean(p)(F) equals the integral of F over the actual cylinder divided by its actual positive M mass, for every original nonempty p and every F in the original G. It also equals the mean of the actual conditional pullback of F to suffix rays.

For every original F, Q(A)F is exactly the orthogonal projection of F onto V(A). In particular Q(A) fixes each indicator indexed by A. The cylinder span is finite dimensional.

Two distinct prefix-free addresses have disjoint actual cylinders. Their indicators are therefore orthogonal, their squared norms are their actual cylinder masses, and each normalized atom mean extracts its own indicator coefficient. Thus Q(A)F lies in the span and F minus Q(A)F is orthogonal to that span, which characterizes the projection.

The actual normalized integral is related to suffix composition by the original measure-preserving map from M to the conditional cylinder law. No preservation of the ambient measure M by prepending is asserted.

**Theorem 1.7 (The Exact Partition Residual).**

$$\forall A: \operatorname{Finset}\left(\operatorname{Edge}\left(\right)\right), ((\operatorname{IsPrefixFree}\left(\operatorname{addresses}\left(A\right)\right)\land \forall omega: \operatorname{Omega}\left(\right), (\exists p: \operatorname{Edge}\left(\right), (p\in A\land omega\in \operatorname{cylinder}\left(\operatorname{val}\left(p\right)\right))))\implies (\forall p\in A, \forall F: \operatorname{G}\left(\right), (\operatorname{pullback}\left(\operatorname{val}\left(p\right), \operatorname{Q}\left(A, F\right)\right)=\operatorname{constG}\left(\operatorname{atomMean}\left(p, F\right)\right)))\land (\forall p\in A, \forall z: \operatorname{H}\left(\right), (\operatorname{pullback}\left(\operatorname{val}\left(p\right), (\operatorname{C}\left(z\right)-\operatorname{Q}\left(A, \operatorname{C}\left(z\right)\right))\right)=\operatorname{C}\left(\operatorname{S}\left(\operatorname{val}\left(p\right), z\right)\right)))\land (\forall F: \operatorname{G}\left(\right), ((\Vert F\Vert)^{2}=\sum_{p\in A} (\operatorname{mass}\left(M, \operatorname{cylinder}\left(\operatorname{val}\left(p\right)\right)\right)\cdot (\Vert \operatorname{pullback}\left(\operatorname{val}\left(p\right), F\right)\Vert)^{2})))\land (\forall z: \operatorname{H}\left(\right), ((\Vert (\operatorname{C}\left(z\right)-\operatorname{Q}\left(A, \operatorname{C}\left(z\right)\right))\Vert)^{2}=\sum_{p\in A} (\operatorname{mass}\left(M, \operatorname{cylinder}\left(\operatorname{val}\left(p\right)\right)\right)\cdot (\Vert \operatorname{C}\left(\operatorname{S}\left(\operatorname{val}\left(p\right), z\right)\right)\Vert)^{2})))\land (\forall c: \operatorname{Real}\left(\right), (\operatorname{Q}\left(A, \operatorname{constG}\left(c\right)\right)=\operatorname{constG}\left(c\right)))\land (\forall F: \operatorname{G}\left(\right), (\operatorname{Q}\left(A, \operatorname{Pi}\left(F\right)\right)=\operatorname{Pi}\left(\operatorname{Q}\left(A, F\right)\right)))\land (\operatorname{dim}\left(\operatorname{V}\left(A\right)\right)=\operatorname{card}\left(A\right)\land \operatorname{dim}\left(\operatorname{V0}\left(A\right)\right)=\operatorname{card}\left(A\right)-1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.partition_centered_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Suppose the finite prefix-free family A covers every original infinite ray. For every p in A and every F in G, the conditional pullback of Q(A)F is the actual constant with value atomMean(p)(F). Consequently, for every original z in H, the conditional pullback of Cz minus Q(A)Cz equals exactly C(S(p)z).

For every F in the original G, its squared norm equals the sum over A of the actual cylinder mass times the squared norm of its conditional pullback. Apply the measure-preserving identification with the normalized restriction separately on each cylinder, then sum the disjoint cylinder integrals over the covering partition. Applying this identity to Cz minus Q(A)Cz gives exactly the weighted sum of the squared norms of C(S(p)z).

The same constructed Q(A) fixes every actual constant and commutes with Pi. The constant identity follows by summing its actual atom values on the partition. Orthogonal symmetry then shows that Q(A) preserves the actual mean, and the formula for Pi gives commutation.

The dimension of V(A) is exactly the number of addresses in A. Indeed applying each actual atom mean to a linear relation among the indicators extracts that indicator's coefficient, so the indicators are linearly independent. The actual mean restricted to V(A) is nonzero because the actual constant one lies in V(A) and has mean one. Rank-nullity therefore gives dimension card(A) minus one for the actual mean-zero subspace V0(A).

**Theorem 1.8 (An Actual Mass Threshold Bound).**

$$\forall A: \operatorname{Finset}\left(\operatorname{Edge}\left(\right)\right), (\forall t: \operatorname{Real}\left(\right), (\forall z: \operatorname{H}\left(\right), ((\operatorname{IsPrefixFree}\left(\operatorname{addresses}\left(A\right)\right)\land \forall omega: \operatorname{Omega}\left(\right), (\exists p: \operatorname{Edge}\left(\right), (p\in A\land omega\in \operatorname{cylinder}\left(\operatorname{val}\left(p\right)\right))))\land 0\leq t\land (\forall p\in A, \operatorname{mass}\left(M, \operatorname{cylinder}\left(\operatorname{val}\left(p\right)\right)\right)\leq t)\implies (\Vert (\operatorname{C}\left(z\right)-\operatorname{Q}\left(A, \operatorname{C}\left(z\right)\right))\Vert)^{2}\leq \operatorname{goldenRatio}\left(\right)\cdot t\cdot (\Vert z\Vert)^{2})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.bounded_partition_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let t be nonnegative. If every actual M cylinder mass in the finite prefix-free covering family A is at most t, then for every original z in H the squared norm of Cz minus Q(A)Cz is at most the golden ratio times t times the squared norm of z. This follows by applying the weighted disjoint-suffix estimate to the exact residual decomposition.

The hypothesis is a bound on the actual cylinder masses. Applying this theorem to every weak first mass crossing for zero less than t less than one additionally requires identifying the actual Bernoulli cylinder masses with the frozen product-mass frontier. The all-threshold specialization, the covariance equality and the spectral counting conclusions are not asserted here.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.Q`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.V`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.V0`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.atomMean`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.bounded_partition_residual`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.cylinder_average_projection`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.cylinder_ray`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection.partition_centered_residual`
- Dependency: [D5/S0/Computability/Coding/BiasedMassFrontier](../../../../S0/Computability/Coding/BiasedMassFrontier.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCentering](BiasedBoundaryCentering.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundarySuffixEnergy](BiasedBoundarySuffixEnergy.md)
