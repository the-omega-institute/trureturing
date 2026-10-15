# Every missing-prefix actual obstruction

## Abstract

Every missing-prefix actual obstruction

The original height is the ordered-tree depth with leaves at zero. Family D consists exactly of outer(v)=pair(alpha,v) with height(v)<=D. PublicMenu prefixes each relative literal by R in the original order. The whole-vector identity holds at every natural update count, including blocked suffixes.

For a missing proper prefix a and selected q=ar with r nonempty, use exactly v=spine(a,alpha), vprime=spine(a,beta). The spine is the original FM.21 context. Its height is length(a), and flipping its reached leaf at a produces the other tree. The existing off-leaf flip invariance therefore supplies equality of every selected initial coordinate.

Take one common k=pathCost(r)+1. Atomic navigation reaches beta from alpha and a branch from beta at r. Originally-present transport is applied at a, then the literal append identity transfers those replies to q. It is never applied at initially absent q. The bound length(q)+1<=D makes k<2D and forces D>=2. At D=1 no such missing-prefix case exists.

**Theorem 1.1 (A common atomic separating count at each address).**

$$\forall r: Address, ((\operatorname{readout}\left(r, \operatorname{iterate}\left(substitution, \operatorname{pathCost}\left(r\right) + 1, \operatorname{of}\left(true\right)\right)\right) = beta) \land (\operatorname{readout}\left(r, \operatorname{iterate}\left(substitution, \operatorname{pathCost}\left(r\right) + 1, \operatorname{of}\left(false\right)\right)\right) = branch))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuObstruction.atomic_separator` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here k=pathCost(r)+1. Guarded atomic navigation reaches beta from alpha and the pair (beta,alpha) from beta at that same literal address and count. The unconditional subtree/readout identity transfers these reached roots to the actual four-valued replies.

**Theorem 1.2 (Whole-vector collision, rank separation and one legal future count).**

$$\forall D: Nat, (\forall S: Menu, ((\forall q: Address, ((q \in S) \implies (\operatorname{length}\left(q\right) + 1 \leq D))) \implies (\forall a, r: Address, (((r \neq \operatorname{nil}\left(\right)) \land (\operatorname{append}\left(a, r\right) \in S) \land (\neg (a \in S))) \implies ((2 \leq D) \land (\operatorname{height}\left(\operatorname{spine}\left(a, \operatorname{of}\left(true\right)\right)\right) = \operatorname{length}\left(a\right)) \land (\operatorname{height}\left(\operatorname{spine}\left(a, \operatorname{of}\left(false\right)\right)\right) = \operatorname{length}\left(a\right)) \land (\operatorname{length}\left(a\right) \leq \operatorname{sub}\left(D, 2\right)) \land (\operatorname{Family}\left(D, \operatorname{outer}\left(\operatorname{spine}\left(a, \operatorname{of}\left(true\right)\right)\right)\right)) \land (\operatorname{Family}\left(D, \operatorname{outer}\left(\operatorname{spine}\left(a, \operatorname{of}\left(false\right)\right)\right)\right)) \land (\operatorname{initial}\left(S, \operatorname{spine}\left(a, \operatorname{of}\left(true\right)\right)\right) = \operatorname{initial}\left(S, \operatorname{spine}\left(a, \operatorname{of}\left(false\right)\right)\right)) \land (\operatorname{initial}\left(\operatorname{publicMenu}\left(S\right), \operatorname{outer}\left(\operatorname{spine}\left(a, \operatorname{of}\left(true\right)\right)\right)\right) = \operatorname{initial}\left(\operatorname{publicMenu}\left(S\right), \operatorname{outer}\left(\operatorname{spine}\left(a, \operatorname{of}\left(false\right)\right)\right)\right)) \land (\operatorname{code}\left(S, \operatorname{spine}\left(a, \operatorname{of}\left(true\right)\right)\right) \neq \operatorname{code}\left(S, \operatorname{spine}\left(a, \operatorname{of}\left(false\right)\right)\right)) \land (\operatorname{pathCost}\left(r\right) + 1 < 2 \times D) \land (\operatorname{readout}\left(\operatorname{cons}\left(true, \operatorname{append}\left(a, r\right)\right), \operatorname{iterate}\left(substitution, \operatorname{pathCost}\left(r\right) + 1, \operatorname{outer}\left(\operatorname{spine}\left(a, \operatorname{of}\left(true\right)\right)\right)\right)\right) = beta) \land (\operatorname{readout}\left(\operatorname{cons}\left(true, \operatorname{append}\left(a, r\right)\right), \operatorname{iterate}\left(substitution, \operatorname{pathCost}\left(r\right) + 1, \operatorname{outer}\left(\operatorname{spine}\left(a, \operatorname{of}\left(false\right)\right)\right)\right)\right) = branch) \land (\operatorname{future}\left(S, \operatorname{spine}\left(a, \operatorname{of}\left(true\right)\right), \operatorname{pathCost}\left(r\right) + 1\right) \neq \operatorname{future}\left(S, \operatorname{spine}\left(a, \operatorname{of}\left(false\right)\right), \operatorname{pathCost}\left(r\right) + 1\right)) \land (\operatorname{future}\left(\operatorname{publicMenu}\left(S\right), \operatorname{outer}\left(\operatorname{spine}\left(a, \operatorname{of}\left(true\right)\right)\right), \operatorname{pathCost}\left(r\right) + 1\right) \neq \operatorname{future}\left(\operatorname{publicMenu}\left(S\right), \operatorname{outer}\left(\operatorname{spine}\left(a, \operatorname{of}\left(false\right)\right)\right), \operatorname{pathCost}\left(r\right) + 1\right)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuObstruction.every_missing_prefix_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These conclusions all concern the same actual pair and the same supplied count. Each history uses its own fixed original source and genuine repeated substitution. Code inequality uses the original branch-first ranks of this pair, including the eta=0 overlap case. No generic quotient, coordinate-specific source choices or resource-efficiency assertion enters the result.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuObstruction.atomic_separator`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuObstruction.every_missing_prefix_obstruction`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeAlphaSpineObservation](NativeAlphaSpineObservation.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeDepthPatterns](NativeDepthPatterns.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuReconstruction](NativeFiniteMenuReconstruction.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedNavigationCompiler](NativeRankedNavigationCompiler.md)
