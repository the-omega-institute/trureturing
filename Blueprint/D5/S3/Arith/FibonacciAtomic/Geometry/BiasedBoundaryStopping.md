# Weak Stopping on the Original Biased Boundary

## Abstract

Every weak mass threshold gives an actual finite cylinder projection and an all-vector residual bound.

**Definition 1.1 (Threshold).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Threshold`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Threshold` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A threshold t is any real number strictly between zero and one. The endpoints are excluded; equality of a cylinder mass with t is included as a stopping event.

**Definition 1.2 (A).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.A`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A(t) is the finite first-crossing frontier, converted to the original edge type of nonempty addresses. An address p belongs exactly when mass(p) is at most t and the mass of p with its last letter deleted is strictly greater than t.

**Definition 1.3 (Qt).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Qt`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Qt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Qt(t) is Q(A(t)), the continuous linear sum of the actual stopping-cylinder indicators multiplied by their normalized actual M integrals. It acts on the original G=L2(M).

**Definition 1.4 (Vt).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Vt`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Vt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vt(t) is the span of those actual cylinder indicators in G, the finite cylinder-constant space.

**Definition 1.5 (Vt0).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Vt0`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Vt0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Vt0(t) is the kernel of the actual mean restricted to Vt(t).

**Definition 1.6 (G0).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.G0`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.G0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

G0 is the kernel of the actual M mean in G, with its inherited subspace structure.

**Theorem 1.7 (The Actual Weak Crossing Partition).**

$$\forall t: \operatorname{Threshold}\left(\right), (\operatorname{IsPrefixFree}\left(\operatorname{A}\left(t\right)\right)\land \operatorname{UniqueCylinderCover}\left(\operatorname{A}\left(t\right), M\right)\land \sum_{p\in \operatorname{A}\left(t\right)} (\operatorname{mass}\left(p\right))=1\land 1/t\leq \operatorname{card}\left(\operatorname{A}\left(t\right)\right)< 1/(b\cdot t))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.actual_stopping_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original address p, including the empty address, the real M mass of its cylinder equals wordMass(letterMass(a,b),p). Both products use a at false and b at true. Here a is the reciprocal golden ratio, b is its square, both are positive, b is at most a, a is less than one, and a+b=1.

For every t between zero and one, the existing first-mass-frontier theorem supplies a finite prefix-free family with exactly the weak condition mass(p)<=t<mass(parent(p)). Every word in it is nonempty. Converting it to the original edge subtype preserves its words, cardinality, product masses and finite depth bound.

An original ray lies in cylinder(p) exactly when p is its prefix of length length(p). The unique frontier prefix on every ray therefore gives a unique actual stopping cylinder. Thus the cylinders cover all of the original ray space and are disjoint.

Every actual stopping mass is strictly greater than b*t and at most t. Their sum is exactly one, and the number k of stopping addresses satisfies 1/t<=k<1/(b*t). These are the same Bernoulli masses and the same nonempty original coordinates used by the boundary trace, including all threshold equality cases.

**Theorem 1.8 (Actual Projection and Residual at Every Threshold).**

$$\forall t: \operatorname{Threshold}\left(\right), ((\forall p\in \operatorname{A}\left(t\right), \forall z: \operatorname{H}\left(\right), (\operatorname{pullback}\left(p, (\operatorname{C}\left(z\right)-\operatorname{Qt}\left(t, \operatorname{C}\left(z\right)\right))\right)=\operatorname{C}\left(\operatorname{S}\left(p, z\right)\right)))\land (\forall z: \operatorname{H}\left(\right), ((\Vert (\operatorname{C}\left(z\right)-\operatorname{Qt}\left(t, \operatorname{C}\left(z\right)\right)) \Vert)^{2}=\sum_{p\in \operatorname{A}\left(t\right)} (\operatorname{mass}\left(p\right)\cdot (\Vert \operatorname{C}\left(\operatorname{S}\left(p, z\right)\right) \Vert)^{2})\leq \operatorname{goldenRatio}\left(\right)\cdot t\cdot (\Vert z \Vert)^{2}))\land \forall F: \operatorname{G}\left(\right), (\operatorname{Qt}\left(t, F\right)=\operatorname{starProjection}\left(\operatorname{Vt}\left(t\right), F\right))\land (\operatorname{dim}\left(\operatorname{Vt}\left(t\right)\right)=\operatorname{card}\left(\operatorname{A}\left(t\right)\right)\land \operatorname{dim}\left(\operatorname{Vt0}\left(t\right)\right)=\operatorname{card}\left(\operatorname{A}\left(t\right)\right)-1)\land (\operatorname{range}\left(\operatorname{restrict}\left(\operatorname{Qt}\left(t\right), G0\right)\right)=\operatorname{intersection}\left(\operatorname{Vt}\left(t\right), G0\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.actual_stopping_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every t between zero and one and every original F in G, Qt(t)F is exactly the orthogonal projection onto Vt(t). Its value on the conditional suffix copy of a stopping cylinder p is the constant atomMean(p)(F), namely the actual integral of F over that cylinder divided by its actual positive M mass.

For every original z in H and every p in A(t), the actual conditional pullback of Cz-Qt(t)Cz is exactly C(S(p)z). The suffix map retains the coordinates z(p++u) for nonempty u only, hence only strict descendants of p. The original empty-prefix path-split identity and the actual centering map remain unchanged.

For every F in the original G, its squared norm is exactly the sum over A(t) of the actual mass of cylinder(p) times the squared norm of its conditional pullback. Applied to Cz-Qt(t)Cz, this is exactly the mass-weighted sum of the squared norms of C(S(p)z). No finite-support restriction on z is imposed.

For every original z in H, the resulting squared residual norm is at most goldenRatio*t times the squared norm of z. The actual stopping masses are at most t, the centered trace bound gives the golden-ratio factor, and the strict-descendant coordinate sets are disjoint. Their total squared edge norm is at most the original squared edge norm, so no additional factor of two occurs.

The same Qt(t) fixes every actual constant and commutes with Pi. Vt(t) has dimension card(A(t)); Vt0(t) has dimension card(A(t))-1. Restricting the domain of Qt(t) to the actual mean-zero subspace G0 gives range exactly Vt(t) intersect G0. Indeed commutation with Pi keeps the output centered, and each centered vector in Vt(t) is fixed by the projection and is its own centered preimage.

The mass-frontier and finite-partition results are applied with their original hypotheses and actual measure. The covariance quadratic-form equality, the comparison operator H, and the spectral and counting statements require separate identifications and are not conclusions of this result.

Compactness and the later spectral counting statements require separate identifications and are not conclusions of this result.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.A`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.G0`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Qt`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Threshold`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Vt`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.Vt0`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.actual_stopping_partition`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryStopping.actual_stopping_residual`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryCylinderProjection](BiasedBoundaryCylinderProjection.md)
