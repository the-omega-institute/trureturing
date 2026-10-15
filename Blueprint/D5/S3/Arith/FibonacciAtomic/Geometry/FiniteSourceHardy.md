# Uniform Native Hardy Tails

## Abstract

The common real edge ell2 maps into each actual source node L2 with a uniform geometric tail.

**Definition 1.1 (Edge).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.Edge`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Edge consists precisely of nonempty original Bool addresses. The empty root is not a coordinate.

**Definition 1.2 (H).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.H`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.H` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

H is lp with exponent two over the real Edge coordinates, common to every source.

**Definition 1.3 (NodeL2).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.NodeL2`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.NodeL2` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

NodeL2(n) is the real Lp space with exponent two for the actual uniform all-occurrence measure mu(n). The codomain depends on n.

**Definition 1.4 (edges).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.edges`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.edges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

edges(n) contains exactly the nonempty addresses occurring in vertices(n).

**Definition 1.5 (path).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.path`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.path` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

path(n,h,x) contains actual nonempty prefixes of x whose length is greater than h.

**Definition 1.6 (value).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.value`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.value` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

value(n,h,z,x) is the sum of z over path(n,h,x). Missing addresses have no term. The value at the root is zero.

**Definition 1.7 (trace).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.trace`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.trace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

trace(n,h,z) is that actual path function in NodeL2(n).

**Definition 1.8 (projectionLinear).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.projectionLinear`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.projectionLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

projectionLinear(h) retains coordinates of length at most h and sets all other coordinates to zero.

**Definition 1.9 (P).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.P`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.P` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

P(h) is the bounded coordinate projection induced by projectionLinear(h).

**Definition 1.10 (J).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.J`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.J` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

J(n) is the actual root-path increment map into NodeL2(n). Its value is trace(n,0,z).

**Theorem 1.11 (Uniform Native Hardy Tails).**

$$((\forall n: \mathbb{N}, (\forall p: \operatorname{Address}\left(\right), (\operatorname{mass}\left(n, p\right) \leq ((2) \cdot (\operatorname{goldenRatio}\left(\right))) \cdot ((a)^{\operatorname{length}\left(p\right)})))) \land (\forall n: \mathbb{N}, (\forall h: \mathbb{N}, (\forall z: \operatorname{H}\left(\right), ((\Vert \operatorname{J}\left(n, (z) - (\operatorname{P}\left(h, z\right))\right) \Vert)^{2} \leq (\frac{((2) \cdot (\operatorname{goldenRatio}\left(\right))) \cdot ((a)^{(h) + (1)})}{(1) - (a)}) \cdot ((\Vert z \Vert)^{2})))))) \land (\forall n: \mathbb{N}, (\forall h: \mathbb{N}, (\Vert \operatorname{comp}\left(\operatorname{J}\left(n\right), (\operatorname{I}\left(\right)) - (\operatorname{P}\left(h\right))\right) \Vert \leq \sqrt{\frac{((2) \cdot (\operatorname{goldenRatio}\left(\right))) \cdot ((a)^{(h) + (1)})}{(1) - (a)}})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.finite_source_hardy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coefficient bound holds for every natural source index and every address. The trace and operator bounds hold for every natural n and h, including zero, on the same real edge ell2. The operator in the final clause is J(n) composed with I-P(h). Each J(n) retains its own actual node L2 codomain.

A root path has at most one prefix of each length. Its weights a to the prefix length therefore sum to at most a to the power h+1 divided by 1-a. Weighted Cauchy-Schwarz bounds the square of the path sum by this weight sum times the sum of squared increments divided by their weights.

Integrating over the actual node probability measure gives each increment its actual descendant mass. The native uniform mass envelope cancels the reciprocal weight. The remaining finite squared-coordinate sum is bounded by the ell2 energy. Taking square roots gives the operator-norm tail.

This finite-source result supplies no boundary measure, limiting trace, compact extension, covariance convergence or screening formula.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.Edge`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.H`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.J`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.NodeL2`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.P`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.edges`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.finite_source_hardy`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.path`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.projectionLinear`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.trace`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceHardy.value`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/FiniteSourceMass](FiniteSourceMass.md)
