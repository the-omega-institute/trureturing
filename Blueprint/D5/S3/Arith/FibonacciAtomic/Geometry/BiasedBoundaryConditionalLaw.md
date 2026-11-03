# The Actual Conditional Suffix Law

## Abstract

Prepending a finite address pushes the actual golden biased Bernoulli law to its normalized restriction, giving a bounded conditional composition on the common boundary L2.

**Definition 1.1 (tail).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.tail`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.tail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Deleting n initial coordinates shifts a ray to its suffix. Under the original infinite product law this suffix again has law M.

**Definition 1.2 (prepend).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.prepend`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.prepend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Prepending p prescribes its original finite coordinates and shifts an arbitrary suffix ray to start after them.

**Definition 1.3 (conditional).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.conditional`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.conditional` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conditional measure is the restriction of the original M to the actual cylinder of p, divided by that cylinder's mass. The mass is positive and finite for every p, including the empty prefix.

**Definition 1.4 (pullbackBound).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.pullbackBound`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.pullbackBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conditional composition bound is the real value of the reciprocal cylinder mass raised to one half.

**Definition 1.5 (pullback).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.pullback`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.pullback` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conditional pullback is a continuous linear map from the original G to itself. It composes a representative with prepend, using the normalized restricted target measure to establish square integrability and independence of representatives.

**Definition 1.6 (conditionalTrace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.conditionalTrace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.conditionalTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The conditional trace composes this bounded pullback with the original all-ell2 trace J, retaining L2(M) as its suffix codomain.

**Theorem 1.7 (Disintegration and Bounded Pullback).**

$$(\forall p: \operatorname{Address}\left(\right), (\operatorname{M}\left(\operatorname{cylinder}\left(p\right)\right)\neq0))\land(\forall p: \operatorname{Address}\left(\right), (\operatorname{map}\left(\operatorname{restrict}\left(M, \operatorname{cylinder}\left(p\right)\right), \operatorname{tail}\left(\operatorname{length}\left(p\right)\right)\right)=(\operatorname{M}\left(\operatorname{cylinder}\left(p\right)\right)) \cdot (M)))\land(\forall p: \operatorname{Address}\left(\right), (\operatorname{MeasurePreserving}\left(\operatorname{prepend}\left(p\right), M, \operatorname{conditional}\left(p\right)\right)))\land(\operatorname{conditional}\left(\operatorname{empty}\left(\right)\right)=M)\land(\forall p: \operatorname{Address}\left(\right), (\forall F: \operatorname{G}\left(\right), (\operatorname{aeEq}\left(M, \operatorname{pullback}\left(p, F\right), \operatorname{compose}\left(F, \operatorname{prepend}\left(p\right)\right)\right))))\land(\forall p: \operatorname{Address}\left(\right), (\forall F: \operatorname{G}\left(\right), (\Vert \operatorname{pullback}\left(p, F\right) \Vert\leq(\operatorname{pullbackBound}\left(p\right)) \cdot (\Vert F \Vert))))\land(\forall p: \operatorname{Address}\left(\right), (\forall z: \operatorname{H}\left(\right), (\operatorname{aeEq}\left(M, \operatorname{conditionalTrace}\left(p, z\right), \operatorname{compose}\left(\operatorname{J}\left(z\right), \operatorname{prepend}\left(p\right)\right)\right))))\land(\forall p: \operatorname{Address}\left(\right), (\forall w: \operatorname{Omega}\left(\right), (\operatorname{tail}\left(\operatorname{length}\left(p\right), \operatorname{prepend}\left(p, w\right)\right)=w)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.conditional_pullback_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite prefix, pushing the restricted measure forward by deletion gives the original law multiplied by the cylinder mass. Equivalently, prepending pushes M to its actual normalized restricted measure. This includes the empty prefix, whose conditional measure is M.

The prescribed finite coordinates and the remaining coordinates are independent under the same infinite product measure. The suffix reindexing has law M. On the prescribed cylinder, prepend after deletion is the identity, which transports the restricted suffix law back to the normalized cylinder law.

For every F in the original G, the pullback equals composition with prepend almost everywhere for M, and its norm is bounded by the reciprocal square root of the cylinder mass times the norm of F. Consequently this representative identity also holds for the joined J applied to every vector of the original H. Deleting a prepended prefix recovers every suffix ray exactly.

The exceptional representative set may depend on the vector. The prefix-constant plus J of strict suffix increments, the mass-stopping conditional projection, the centered residual identity and its weighted norm decomposition require additional proofs. No spectral operator or counting result is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.conditional`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.conditionalTrace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.conditional_pullback_law`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.prepend`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.pullback`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.pullbackBound`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw.tail`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrace](BiasedBoundaryTrace.md)
