# Native Ancestor Area Choices

## Abstract

Independent bracket choices in a native Fibonacci source preserve the leaf word and have an exact affine ancestor-area formula.

Sources are nonempty ordered binary trees with beta and alpha leaves. The canonical source T at generation n is the n-fold Fibonacci substitution of alpha. The left-associated source B and the right-associated source D both have leaf word beta, alpha, beta.

**Definition 1.1 (The canonical three-leaf source).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.defectB`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.defectB` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

B is pair(pair(beta,alpha),beta).

**Definition 1.2 (The bracket defect).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.defectD`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.defectD` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

D is pair(beta,pair(alpha,beta)).

**Definition 1.3 (All literal three-leaf positions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.positions`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.positions` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

positions(t) consists of every actual address whose subtree in t is B.

**Definition 1.4 (Simultaneous native choices).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.fill`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.fill` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fill(t,a) replaces B by D precisely at the original positions where the Boolean choice a is true.

**Definition 1.5 (The finite-subset family).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.variant`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.variant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

variant(t,A) uses the membership indicator of A as the simultaneous choice.

**Theorem 1.6 (The subtree at an original position).**

$$\forall t: \operatorname{Source}, (\forall a: \operatorname{Address} \to \operatorname{Bool}, (\forall p: \operatorname{Address}, ((\operatorname{Member}\left(p, \operatorname{positions}\left(t\right)\right)) \implies (\operatorname{subtree}\left(p, \operatorname{fill}\left(t, a\right)\right) = \operatorname{some}\left(\operatorname{ite}\left(\operatorname{a}\left(p\right), \operatorname{defectD}, \operatorname{defectB}\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.fill_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every original B position remains present after simultaneous filling. Its subtree is exactly D for a true choice and B for a false choice.

**Definition 1.7 (Euclidean ancestor-area vector).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.areaVector`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.areaVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

areaVector(m,t) lists the products of the left and right child leaf counts in inorder gap order, in Euclidean space with m minus one coordinates. Unoccupied coordinates are zero.

**Definition 1.8 (One unit of transferred area).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.gapVector`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.gapVector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

gapVector(m,j) is the standard unit vector at j minus the standard unit vector at j plus one.

**Definition 1.9 (The actual source family).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.sourceFamily`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.sourceFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

sourceFamily(t) is the image of the full powerset of positions(t) under variant(t).

**Definition 1.10 (The complete Euclidean vertex set).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.areaVertices`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.areaVertices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

areaVertices(t) is the image of the same powerset under the ancestor-area vector.

**Definition 1.11 (The normalized Euclidean family).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.normalizedAreaFamily`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.normalizedAreaFamily` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The area vertices of T(n) are scaled by the reciprocal of choose(fib(n plus one),two).

**Definition 1.12 (Normalized independent directions).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.unitDirection`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.unitDirection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each signed gap vector is divided by square root two.

**Definition 1.13 (The direction space).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.directionSpan`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.directionSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real span of the normalized gap vectors is the Euclidean direction space of the cube.

**Definition 1.14 (The cube in its own direction space).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.intrinsicCube`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.intrinsicCube` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the inverse image of the convex hull under x maps to areaVector(t) plus x, with x in directionSpan(t). Its volume is the canonical Euclidean volume on that subspace.

**Theorem 1.15 (The native family, area formula and squared distances).**

$$\forall n: \mathbb{N}, ((3 \le n) \implies ((\operatorname{card}\left(\operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right) = \operatorname{fib}\left(n-2\right)) \land ((\operatorname{InjectiveOn}\left(\operatorname{variant}\left(\operatorname{T}\left(n\right)\right), \operatorname{powerset}\left(\operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)\right)) \land ((\forall A: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(A, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies ((\operatorname{wd}\left(\operatorname{variant}\left(\operatorname{T}\left(n\right), A\right)\right) = \operatorname{wd}\left(\operatorname{T}\left(n\right)\right)) \land ((\operatorname{length}\left(\operatorname{variant}\left(\operatorname{T}\left(n\right), A\right)\right) = \operatorname{fib}\left(n+1\right)) \land ((\operatorname{depth}\left(\operatorname{variant}\left(\operatorname{T}\left(n\right), A\right)\right) = \operatorname{ite}\left(A = \emptyset, n, 0\right)) \land ((\operatorname{areaVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{variant}\left(\operatorname{T}\left(n\right), A\right)\right) = \operatorname{areaVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{T}\left(n\right)\right)+\sum_{p \in A} \operatorname{gapVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{offset}\left(\operatorname{T}\left(n\right), p\right)\right)) \land ((\sum_{i:\operatorname{Fin}\left(\operatorname{fib}\left(n+1\right)-1\right)} \operatorname{areaVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{variant}\left(\operatorname{T}\left(n\right), A\right), i\right) = \operatorname{choose}\left(\operatorname{fib}\left(n+1\right), 2\right)) \land ((\operatorname{length}\left(\operatorname{coordinates}\left(\operatorname{variant}\left(\operatorname{T}\left(n\right), A\right)\right)\right) = \operatorname{fib}\left(n+1\right)-1) \land (\forall B: \operatorname{Finset}\left(\operatorname{Address}\right), ((\operatorname{Subset}\left(B, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies (\operatorname{norm}\left(\operatorname{areaVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{variant}\left(\operatorname{T}\left(n\right), A\right)\right)-\operatorname{areaVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{variant}\left(\operatorname{T}\left(n\right), B\right)\right)\right)^{2} = 2\times\operatorname{card}\left(\operatorname{symmDiff}\left(A, B\right)\right)))))))))))) \land ((\forall p: \operatorname{Address}, (\operatorname{Iff}\left(\operatorname{mem}\left(p, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right), \operatorname{subtree}\left(p, \operatorname{T}\left(n\right)\right) = \operatorname{some}\left(\operatorname{defectB}\right)\right))) \land ((\forall p: \operatorname{Address}, ((\operatorname{mem}\left(p, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies ((\operatorname{offset}\left(\operatorname{T}\left(n\right), p\right) < \operatorname{fib}\left(n+1\right)-1) \land (\operatorname{offset}\left(\operatorname{T}\left(n\right), p\right)+1 < \operatorname{fib}\left(n+1\right)-1)))) \land ((\forall p: \operatorname{Address}, ((\operatorname{mem}\left(p, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies (\forall q: \operatorname{Address}, ((\operatorname{mem}\left(q, \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)) \implies ((p \neq q) \implies ((\operatorname{offset}\left(\operatorname{T}\left(n\right), p\right)+3 \le \operatorname{offset}\left(\operatorname{T}\left(n\right), q\right)) \lor (\operatorname{offset}\left(\operatorname{T}\left(n\right), q\right)+3 \le \operatorname{offset}\left(\operatorname{T}\left(n\right), p\right)))))))) \land ((\operatorname{convexHull}\left(\mathbb{R}, \operatorname{areaVertices}\left(\operatorname{T}\left(n\right)\right)\right) = \operatorname{singleton}\left(\operatorname{areaVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{T}\left(n\right)\right)\right)+\operatorname{parallelepiped}\left(p:\operatorname{positions}\left(\operatorname{T}\left(n\right)\right) \mapsto \operatorname{gapVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{offset}\left(\operatorname{T}\left(n\right), p\right)\right)\right)) \land ((\operatorname{direction}\left(\operatorname{affineSpan}\left(\mathbb{R}, \operatorname{convexHull}\left(\mathbb{R}, \operatorname{areaVertices}\left(\operatorname{T}\left(n\right)\right)\right)\right)\right) = \operatorname{directionSpan}\left(\operatorname{T}\left(n\right)\right)) \land ((\operatorname{Orthonormal}\left(\mathbb{R}, \operatorname{unitDirection}\left(\operatorname{T}\left(n\right)\right)\right)) \land ((\operatorname{directionSpan}\left(\operatorname{T}\left(n\right)\right) = \operatorname{span}\left(\mathbb{R}, \operatorname{range}\left(p:\operatorname{positions}\left(\operatorname{T}\left(n\right)\right) \mapsto \operatorname{gapVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{offset}\left(\operatorname{T}\left(n\right), p\right)\right)\right)\right)) \land ((\operatorname{finrank}\left(\mathbb{R}, \operatorname{directionSpan}\left(\operatorname{T}\left(n\right)\right)\right) = \operatorname{fib}\left(n-2\right)) \land ((\forall p: \operatorname{positions}\left(\operatorname{T}\left(n\right)\right), (\operatorname{norm}\left(\operatorname{gapVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{offset}\left(\operatorname{T}\left(n\right), p\right)\right)\right) = \operatorname{sqrt}\left(2\right))) \land (\operatorname{volume}\left(\operatorname{intrinsicCube}\left(\operatorname{T}\left(n\right)\right)\right) = \operatorname{ofReal}\left(2^{\frac{\operatorname{fib}\left(n-2\right)}{2}}\right)))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.native_area_cube` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least three, all B positions are counted by fib(n minus two). Distinct subsets give distinct actual trees. Every choice preserves the leaf word and the fib(n plus one) leaf count. The empty subset has intrinsic substitution depth n, and every nonempty subset has depth zero.

Coordinates record the product of the two child leaf counts at each internal gap. Replacing B changes its two internal coordinates from [1,2] to [2,1]. An arbitrary context with equal-length fillings has the same exterior coordinate lists. Adding positions one at a time gives the stated sum of signed gap vectors. Distinct positions occupy disjoint gap pairs. Squared Euclidean distance is twice the cardinality of the symmetric difference of the choices, and total area is preserved.

The convex hull is the translate of the parallelepiped of the independent signed gap vectors: its coefficients range independently from zero to one. After division by square root two these vectors are orthonormal. Their direction span has dimension fib(n minus two), every edge has length square root two, and the canonical volume in that direction space is two to the power fib(n minus two) divided by two.

**Theorem 1.16 (Exact normalized diameter and decay).**

$$(\forall n: \mathbb{N}, ((3 \le n) \implies ((\operatorname{diam}\left(\operatorname{normalizedAreaFamily}\left(n\right)\right) = \frac{\operatorname{sqrt}\left(2\times\operatorname{fib}\left(n-2\right)\right)}{\operatorname{choose}\left(\operatorname{fib}\left(n+1\right), 2\right)}) \land ((\operatorname{card}\left(\operatorname{sourceFamily}\left(\operatorname{T}\left(n\right)\right)\right) = 2^{\operatorname{fib}\left(n-2\right)}) \land (((\operatorname{depth}\left(\operatorname{variant}\left(\operatorname{T}\left(n\right), \emptyset\right)\right) = n) \land (\operatorname{depth}\left(\operatorname{variant}\left(\operatorname{T}\left(n\right), \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)\right) = 0)) \land (\operatorname{norm}\left(\operatorname{choose}\left(\operatorname{fib}\left(n+1\right), 2\right)^{-1}\times\operatorname{areaVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{variant}\left(\operatorname{T}\left(n\right), \emptyset\right)\right)-\operatorname{choose}\left(\operatorname{fib}\left(n+1\right), 2\right)^{-1}\times\operatorname{areaVector}\left(\operatorname{fib}\left(n+1\right), \operatorname{variant}\left(\operatorname{T}\left(n\right), \operatorname{positions}\left(\operatorname{T}\left(n\right)\right)\right)\right)\right) = \operatorname{diam}\left(\operatorname{normalizedAreaFamily}\left(n\right)\right))))))) \land ((\operatorname{IsBigO}\left(\operatorname{atTop}, n \mapsto \operatorname{diam}\left(\operatorname{normalizedAreaFamily}\left(n\right)\right), n \mapsto \operatorname{fib}\left(n+1\right)^{-\frac{3}{2}}\right)) \land (\operatorname{Tendsto}\left(n \mapsto \operatorname{diam}\left(\operatorname{normalizedAreaFamily}\left(n\right)\right), \operatorname{atTop}, \operatorname{nhds}\left(0\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.normalized_cube_diameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty and full subsets attain the maximal Euclidean separation. Scaling by the reciprocal total area gives the exact normalized diameter. There remain two to the power fib(n minus two) distinct sources, with depth n at the empty choice and zero at the full choice.

Writing M for fib(n plus one) and K for fib(n minus two), the inequalities K at most M and choose(M,two) at least M squared divided by four bound the diameter by four times square root two times M to the power minus three halves. Since the Fibonacci leaf count diverges, the diameter tends to zero.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.areaVector`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.areaVertices`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.defectB`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.defectD`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.directionSpan`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.fill`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.fill_at`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.gapVector`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.intrinsicCube`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.native_area_cube`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.normalizedAreaFamily`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.normalized_cube_diameter`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.positions`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.sourceFamily`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.unitDirection`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.variant`
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualHistorySingleHoleRecovery](../ActualHistorySingleHoleRecovery.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualImageAlphaSeparation](../ActualImageAlphaSeparation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity](../ActualLeafHistoryRigidity.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInterval](AncestorAreaInterval.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/NativeRotationDepthGap](../SourceCoordinates/NativeRotationDepthGap.md)
