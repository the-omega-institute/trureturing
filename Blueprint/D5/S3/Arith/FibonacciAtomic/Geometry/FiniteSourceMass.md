# Actual Fibonacci Descendant Masses

## Abstract

Original guarded address geometry and uniform all-occurrence cylinder masses.

**Definition 1.1 (vertices).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.vertices`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.vertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

vertices(n) contains every original occurrence address of T(n), with the root included.

**Definition 1.2 (N).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.N`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.N` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(n) is the cardinality of vertices(n).

**Definition 1.3 (Node).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.Node`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.Node` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Node(n) is the subtype of actual occurrence addresses of T(n).

**Definition 1.4 (μ).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.μ`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.μ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

mu(n) is the uniform probability measure on Node(n); it assigns equal mass to roots, branches and both terminal labels.

**Definition 1.5 (descendants).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.descendants`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.descendants` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

descendants(n,p) filters vertices(n) by the original prefix relation.

**Definition 1.6 (mass).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.mass`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

mass(n,p) is the cardinality of descendants(n,p) divided by N(n).

**Definition 1.7 (a).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.a`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.a` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

a is the reciprocal of the real golden ratio.

**Theorem 1.8 (Actual Fibonacci Descendant Masses).**

$$((((((((\forall n: \mathbb{N}, (\forall p: \operatorname{Address}\left(\right), ((p \neq []) \implies ((\exists U: \operatorname{Source}\left(\right), (\operatorname{subtree}\left(p, \operatorname{T}\left(n\right)\right) = \operatorname{some}\left(U\right))) \iff ((\operatorname{pathCost}\left(p\right) \leq n) \land ((\operatorname{pathCost}\left(\operatorname{dropLast}\left(p\right)\right)) + (2) \leq n)))))) \land (\forall n: \mathbb{N}, (\forall p: \operatorname{Address}\left(\right), ((p \neq []) \implies ((\operatorname{pathCost}\left(p\right) \leq n) \implies (((\operatorname{pathCost}\left(\operatorname{dropLast}\left(p\right)\right)) + (2) \leq n) \implies ((\operatorname{subtree}\left(p, \operatorname{T}\left(n\right)\right) = \operatorname{some}\left(\operatorname{T}\left((n) - (\operatorname{pathCost}\left(p\right))\right)\right)) \land (\operatorname{mass}\left(n, p\right) = \frac{\operatorname{N}\left((n) - (\operatorname{pathCost}\left(p\right))\right)}{\operatorname{N}\left(n\right)})))))))) \land (\forall n: \mathbb{N}, (\forall p: \operatorname{Address}\left(\right), ((\operatorname{subtree}\left(p, \operatorname{T}\left(n\right)\right) = \operatorname{none}\left(\right)) \implies (\operatorname{mass}\left(n, p\right) = 0))))) \land (\forall n: \mathbb{N}, (\forall p: \operatorname{Address}\left(\right), (\operatorname{mass}\left(n, p\right) \leq ((2) \cdot (\operatorname{goldenRatio}\left(\right))) \cdot ((a)^{\operatorname{length}\left(p\right)}))))) \land (\forall n: \mathbb{N}, (\forall p: \operatorname{Address}\left(\right), (\operatorname{descendantMeasure}\left(n, p\right) = \operatorname{mass}\left(n, p\right))))) \land (\forall n: \mathbb{N}, (\forall x: \operatorname{Node}\left(n\right), (\operatorname{pointMeasure}\left(n, x\right) = \frac{1}{\operatorname{N}\left(n\right)})))) \land (\forall n: \mathbb{N}, (\forall p: \operatorname{Address}\left(\right), ((\operatorname{subtree}\left(p, \operatorname{T}\left(n\right)\right) = \operatorname{some}\left(\operatorname{T}\left((n) - (\operatorname{pathCost}\left(p\right))\right)\right)) \implies (\operatorname{readout}\left(p, \operatorname{T}\left(n\right)\right) = \operatorname{label}\left((n) - (\operatorname{pathCost}\left(p\right))\right)))))) \land (\forall n: \mathbb{N}, (\forall p: \operatorname{Address}\left(\right), (\forall b: \operatorname{Bool}\left(\right), ((\operatorname{subtree}\left(p, \operatorname{T}\left(n\right)\right) = \operatorname{some}\left(\operatorname{of}\left(b\right)\right)) \implies (\forall q: \operatorname{Address}\left(\right), ((q \neq []) \implies (\operatorname{subtree}\left(\operatorname{append}\left(p, q\right), \operatorname{T}\left(n\right)\right) = \operatorname{none}\left(\right))))))))) \land (\forall n: \mathbb{N}, ((\operatorname{mass}\left(n, []\right) = 1) \land (\operatorname{readout}\left([], \operatorname{T}\left(n\right)\right) = \operatorname{label}\left(n\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.finite_source_masses` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

False denotes a left edge and true denotes a right edge. The inherited pathCost adds one for left and two for right. dropLast removes the final edge. A descent is permitted only from a branch, so both the final cost and the last-parent cost plus two must be at most n.

In the formula, label(d) is alpha for d=0, beta for d=1 and branch for d>=2. descendantMeasure(n,p) denotes the real value of mu(n) on the actual nodes whose addresses extend p. pointMeasure(n,x) is the extended nonnegative point mass of x. These quantities use all occurrences, including internal nodes and the root.

The guarded native navigation identifies the entire residual source at each reached address. Prefixing its node enumeration gives the actual ambient descendant set. The original node count is twice the Fibonacci leaf count minus one. Its recurrence yields golden-ratio upper and lower bounds, and their ratio gives the uniform envelope. An absent prefix has no descendants. A terminal cannot be crossed by a further nonempty suffix.

The two singleton sources are retained: the root is alpha at n=0 and beta at n=1. Both have total mass one.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.N`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.Node`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.a`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.descendants`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.finite_source_masses`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.mass`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.vertices`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass.μ`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionHorizon](../Observer/ActualCompletionHorizon.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedNavigationCompiler](../Observer/NativeRankedNavigationCompiler.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap](../SourceCoordinates/NativeRotationDepthGap.md)
