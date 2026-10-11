# Ancestor Area and Intrinsic Depth Instability

## Abstract

The prescribed native Fibonacci trees have equal complete leaf words and unbounded intrinsic-depth gaps despite a fixed ancestor-area distance and vanishing normalized distance.

The sources are the existing FreeMagma Bool trees: true denotes alpha, false denotes beta, and pairing preserves both child order and every leaf label. The coordinate list is the existing inorder ancestor-area list, with each internal node contributing the product of its actual child leaf counts at its own gap.

**Definition 1.1 (Intrinsic inverse-substitution depth).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.depth`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.depth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

depth(t) is the supremum of the natural exponents k for which an actual source p satisfies substitution iterated k times on p equals t. The proof establishes that this set is finite and nonempty for every source. Its supremum is therefore attained and is the maximal actual inverse-substitution exponent. It is not the height of an address.

**Definition 1.2 (The alpha generation ray).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.T`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.T` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

T(n) is substitution iterated n times on the alpha leaf.

**Definition 1.3 (The prescribed rotated sources).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.rotated`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.rotated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rotated(0) is pair(beta,pair(alpha,beta)). The recursive member rotated(k+1) is pair(rotated(k),T(k+2)). Thus the leftmost three-leaf subtree is rotated once, while every appended right subtree is retained.

**Definition 1.4 (Indexing by generation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.U`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.U` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

U(n) is rotated(n-3). For every n at least three, U(3) is pair(beta,pair(alpha,beta)) and U(n+1) is pair(U(n),T(n-1)). The extension to n below three is unused by the family assertions.

**Definition 1.5 (The full ancestor-area readout).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.readout`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.readout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

readout(m,t) casts the existing coordinate list to real values at each gap position. At the actual leaf count m=length(t), the coordinate list has exactly m-1 entries, so no padding contributes. Default zero is used only for indices outside the list. In the displayed statement, real(k) is the canonical natural-to-real cast.

**Definition 1.6 (Total-area normalization).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.normalized`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.normalized` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

normalized(m,t) divides every coordinate of readout(m,t) by the natural binomial coefficient choose(m,2), cast to the reals. For the prescribed sources at n at least three, m=fib(n+1) and this denominator is positive.

**Definition 1.7 (Euclidean distance).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.ltwo`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.ltwo` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ltwo(x,y) is the square root of the sum over all Fin(m-1) positions of the square of x(i)-y(i). The norm of the full vector in the theorem is the ordinary finite product supremum norm.

**Definition 1.8 (A common noisy observation).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.midpoint`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.midpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

midpoint(n) is the coordinatewise arithmetic mean of the two full normalized vectors, using the common leaf count length(T(n)). Exactly this same vector is passed to both error tests and to every summary-to-real estimator.

**Theorem 1.9 (The Full Family and Its Readout Bounds).**

$$(\forall n: \mathbb{N}, ((3 \leq n) \implies ((\operatorname{wd}\left(\operatorname{T}\left(n\right)\right) = \operatorname{wd}\left(\operatorname{U}\left(n\right)\right)) \land ((\operatorname{length}\left(\operatorname{T}\left(n\right)\right) = \operatorname{fib}\left(n + 1\right)) \land ((\operatorname{length}\left(\operatorname{U}\left(n\right)\right) = \operatorname{length}\left(\operatorname{T}\left(n\right)\right)) \land ((\operatorname{depth}\left(\operatorname{T}\left(n\right)\right) = n) \land ((\operatorname{depth}\left(\operatorname{U}\left(n\right)\right) = 0) \land ((\operatorname{ltwo}\left(\operatorname{readout}\left(\operatorname{length}\left(\operatorname{T}\left(n\right)\right), \operatorname{T}\left(n\right)\right), \operatorname{readout}\left(\operatorname{length}\left(\operatorname{T}\left(n\right)\right), \operatorname{U}\left(n\right)\right)\right) = \sqrt{2}) \land ((\Vert (\operatorname{readout}\left(\operatorname{length}\left(\operatorname{T}\left(n\right)\right), \operatorname{T}\left(n\right)\right)) - (\operatorname{readout}\left(\operatorname{length}\left(\operatorname{T}\left(n\right)\right), \operatorname{U}\left(n\right)\right)) \Vert = 1) \land (\Vert (\operatorname{normalized}\left(\operatorname{length}\left(\operatorname{T}\left(n\right)\right), \operatorname{T}\left(n\right)\right)) - (\operatorname{normalized}\left(\operatorname{length}\left(\operatorname{T}\left(n\right)\right), \operatorname{U}\left(n\right)\right)) \Vert = \frac{1}{\operatorname{real}\left(\operatorname{choose}\left(\operatorname{fib}\left(n + 1\right), 2\right)\right)})))))))))) \land ((\neg (\exists L: \mathbb{R}, (\forall s: \operatorname{Source}, (\forall t: \operatorname{Source}, ((\operatorname{length}\left(s\right) = \operatorname{length}\left(t\right)) \implies (\lvert (\operatorname{real}\left(\operatorname{depth}\left(s\right)\right)) - (\operatorname{real}\left(\operatorname{depth}\left(t\right)\right)) \rvert \leq L \cdot \operatorname{ltwo}\left(\operatorname{readout}\left(\operatorname{length}\left(s\right), s\right), \operatorname{readout}\left(\operatorname{length}\left(s\right), t\right)\right))))))) \land ((\operatorname{Tendsto}\left(\lambda n: \mathbb{N}, \frac{1}{\operatorname{real}\left(\operatorname{choose}\left(\operatorname{fib}\left(n + 1\right), 2\right)\right)}, \operatorname{atTop}, \operatorname{nhds}\left(0\right)\right)) \land (\forall n: \mathbb{N}, ((3 \leq n) \implies (\forall epsilon: \mathbb{R}, ((\frac{1}{2 \cdot \operatorname{real}\left(\operatorname{choose}\left(\operatorname{fib}\left(n + 1\right), 2\right)\right)} \leq epsilon) \implies ((\Vert (\operatorname{midpoint}\left(n\right)) - (\operatorname{normalized}\left(\operatorname{length}\left(\operatorname{T}\left(n\right)\right), \operatorname{T}\left(n\right)\right)) \Vert \leq epsilon) \land ((\Vert (\operatorname{midpoint}\left(n\right)) - (\operatorname{normalized}\left(\operatorname{length}\left(\operatorname{T}\left(n\right)\right), \operatorname{U}\left(n\right)\right)) \Vert \leq epsilon) \land (\forall E: (\operatorname{Fin}\left((\operatorname{length}\left(\operatorname{T}\left(n\right)\right)) - (1)\right) \to \mathbb{R}) \to \mathbb{R}, (\frac{\operatorname{real}\left(n\right)}{2} \leq \operatorname{max}\left(\lvert (\operatorname{E}\left(\operatorname{midpoint}\left(n\right)\right)) - (\operatorname{real}\left(\operatorname{depth}\left(\operatorname{T}\left(n\right)\right)\right)) \rvert, \lvert (\operatorname{E}\left(\operatorname{midpoint}\left(n\right)\right)) - (\operatorname{real}\left(\operatorname{depth}\left(\operatorname{U}\left(n\right)\right)\right)) \rvert\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every n at least three, T(n) and U(n) have the same complete ordered leaf word and fib(n+1) leaves. Their intrinsic depths are n and zero. Their full coordinate lists are [1,2] followed by a common tail and [2,1] followed by that same tail. The difference at the first two actual gaps is therefore (-1,1), with zero difference at every later gap. Its Euclidean norm is sqrt(2) and its supremum norm is one.

The simultaneous full-family assertion comes from the actual source recursion. The generation ray obeys T(n+2)=pair(T(n+1),T(n)). The rotated sources have no substitution preimage: the three-leaf member has none, and every subsequent pair retains that obstruction in its left child. Injectivity of native substitution and the absence of an alpha preimage give the maximal depth n of T(n). Finiteness of all actual entrances supplies the maximum defining depth for every source.

The proof directly uses GeometryEntranceRatio.entranceFinite for actual entrance finiteness, SourceTransportCentralizer.source_transport_centralizer for substitution injectivity and the native ray recurrence, CliffordLeafOrbit.result for the ray composition, and the positive atomic-block clause of GraftAffineClosure.result for its Fibonacci components. Leaf-count and coordinate-list length identities are internal interface normalization, not separately delivered theorems or claimed new content.

No finite real L bounds the intrinsic-depth difference of every equal-leaf-count pair by L times its Euclidean ancestor-area distance. Applying such a bound to this prescribed family would force every n at least three to be at most L*sqrt(2).

Dividing the full vectors by choose(fib(n+1),2) gives supremum difference exactly its reciprocal. The reciprocal tends to zero as n tends to infinity. The depth difference remains n. For every permitted coordinate-error tolerance epsilon at least half that reciprocal, the same midpoint lies within epsilon of both exact normalized vectors.

Every real-valued function of that common summary has, on at least one of the two sources, depth error at least n/2. The triangle inequality bounds the sum of its errors below by n, so their maximum is at least n/2. This assertion concerns this ancestor-area readout and its stated coordinate error model; it supplies no lower bound for other observation methods or for acquiring, executing, or storing an observation.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.T`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.U`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.depth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.ltwo`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.midpoint`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.normalized`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.readout`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.result`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability.rotated`
- Dependency: [D5/S3/Arith/FibonacciAtomic/CliffordLeafOrbit](../CliffordLeafOrbit.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval](AncestorAreaInterval.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/GeometryEntranceRatio](GeometryEntranceRatio.md)
