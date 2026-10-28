# Recursive decomposition of unrestricted native image languages

## Abstract

NativeImageSaturationInterface

**Theorem 1.1 (Actual native images split into bounded terminals and recursive pairs).**

$$\forall k: Nat, (\forall X: CompletionTree, ((\operatorname{NativeImage}\left(k, X\right)) \iff ((X = \operatorname{atomic}\left(k\right)) \lor ((X = \operatorname{atomic}\left(k+1\right)) \lor (\exists U: CompletionTree, (\exists V: CompletionTree, ((X = \operatorname{node}\left(U, V\right)) \land (\operatorname{NativeImage}\left(k, U\right)) \land (\operatorname{NativeImage}\left(k, V\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeImageSaturationInterface.native_image_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NativeImage(k,X) means that X is the actual image of some unrestricted completed native tree under rho iterated k times. The domain is the existing PFunctor.M completion: finite trees, arbitrary infinite trees, and the leafless Omega all remain in scope. No source-size, depth, rationality, or finite-prefix bound is introduced.

For every k and X, actual image membership has exactly three alternatives. X is the alpha atomic iterate atomic(k), X is the beta atomic iterate atomic(k+1), or X is an ordered pair whose two children are themselves actual k-images. The pair alternative preserves ordered children and repeated values; it is a structural recursive clause, not an enumeration of finite trees.

The forward direction analyzes the unrestricted preimage at its root. A leaf becomes one of the two atomic terminals, while a pair remains a pair because rho distributes over both children. The reverse direction constructs a preimage for each terminal and combines preimages of both children into one ordered pair. Injectivity and the native iterate identities are retained through the existing CompletionHomogeneousFixedPoints declarations.

This is the image-language interface needed by finite-exception saturation: terminal matches are bounded to the two consecutive atomic values, while all nonterminal obligations recurse on both actual children. The guarded free extension and simultaneous image saturation results use this decomposition on normalized systems. Root-link normalization, its two original solution correspondences and the transport of every original filter and reconstruction are separate requirements for applying that guarded result to the original functional class.

The result is an unrestricted structural theorem over the native completion. It is not a fixed-instance certificate, bounded enumeration, checker, numeric reduction, or claim that all solutions collapse to canonical assignments.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeImageSaturationInterface.native_image_iff`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/CompletionHomogeneousFixedPoints](../CompletionHomogeneousFixedPoints.md)
