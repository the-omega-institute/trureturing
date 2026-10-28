# Cylinder Energies on the Original Boundary

## Abstract

Constant traces have unit fixed-root minimum on the original biased boundary, and the depth-two and depth-one cylinder indicators have mixed free-root energy one eighth.

**Definition 1.1 (rootEdge).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.rootEdge`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.rootEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a Boolean letter c, rootEdge(c) is the original nonempty one-letter address [c]. False denotes L and true denotes R.

**Theorem 1.2 (The Constant-Trace Minimum).**

$$\exists q: H, ((\operatorname{J}\left(q\right)=\operatorname{constG}\left(1\right))\land ((\Vert q \Vert)^{2}=1)\land (\forall c: \mathbb{R}, (\forall z: H, (\operatorname{J}\left(z\right)=\operatorname{constG}\left(c\right)\implies \operatorname{inner}\left(q, z\right)=c)))\land (\forall c: \operatorname{Bool}\left(\right), ((\operatorname{eval}\left(q, \operatorname{rootEdge}\left(c\right)\right)=\frac{1}{2})\land (\operatorname{S}\left([c], q\right)=\frac{1}{2}\cdot q))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.constant_trace_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

H is the original real square-summable space on nonempty ordered Boolean addresses. J maps H to real L2 of the golden biased product measure M. Constants, conditional suffixes and all equalities of traces use this same M.

Project the sum of the two unit root increments onto the orthogonal complement of the kernel of J. The result has constant trace one and is the fixed-root minimum. Pairing it with any constant trace c gives c times its squared norm.

The adjoints of the two original suffix restrictions insert disjoint strict-descendant increments. Their pairing formula gives an exact decomposition of squared edge norm into the two root squares and the two suffix squared norms. Conditional pullback gives the corresponding decomposition of the actual trace.

Write m for the squared norm of the minimum. Inserting half of it below each root edge, with root increments one half, gives another constant-one trace of squared norm (1+m)/2. Minimality gives m at most one. Applying minimality to the two suffixes of the minimum and completing their two squares gives m at least one. The squared norm is therefore one. Equality identifies the inserted vector with the minimum and gives both equal-split identities.

Consequently every original increment vector with constant trace c has squared norm at least c squared. The pairing identity applies to all such vectors, not just finite increments or traces defined pointwise on every ray.

**Definition 1.3 (cylinderD).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.cylinderD`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.cylinderD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For any original nonempty edge p, cylinderD(p) is its actual cylinder indicator in the original free-root domain D. Root coefficient zero and the unit single-edge increment give its domain membership.

**Theorem 1.4 (The Mixed Cylinder Energy).**

$$\operatorname{form}\left(\operatorname{cylinderD}\left(\operatorname{descendant}\left([false], \operatorname{rootEdge}\left(false\right)\right)\right), \operatorname{cylinderD}\left(\operatorname{rootEdge}\left(false\right)\right)\right)=\frac{1}{8}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.mixed_cylinder_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A is the actual indicator of [L] and B is the actual indicator of [LL]. The form pairs their unique effective least-increment lifts in the original free-root domain, with the root coefficient optimized freely.

For A, the root coefficient is one half, its two root increments are one quarter and minus one quarter, and its strict suffixes are these same multiples of the constant-one minimum. For B, the root coefficient is one quarter and the two root increments are one eighth and minus one eighth. At the next level the increments are five sixteenths, minus three sixteenths, minus one sixteenth and minus one sixteenth; each corresponding strict suffix is that increment times the constant-one minimum.

The conditional pullbacks identify these traces with the original two indicators. Pairing either increment vector with an arbitrary vector in the kernel of the centered trace cancels at every junction and at the free root. Both vectors therefore lie in the original effective space K. The existing attained free-root variational theorem identifies them with the actual lifts.

The root edges contribute one sixteenth to their inner product. The left suffix contributes one thirty-second and the right suffix contributes one thirty-second, giving one eighth. This identity is an energy statement on the original form; a real-time non-Markov law requires its further process-law argument.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.constant_trace_minimum`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.cylinderD`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.mixed_cylinder_energy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderEnergy.rootEdge`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryFreeRootForm](BiasedBoundaryFreeRootForm.md)
