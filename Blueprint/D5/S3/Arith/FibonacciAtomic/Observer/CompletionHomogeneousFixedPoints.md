# Exhaustive completed homogeneous fixed-point split

## Abstract

CompletionHomogeneousFixedPoints

**Theorem 1.1 (A homogeneous feedback equation has exactly the leafless solution or the atomic orbit).**

$$\forall a: Nat, (\forall H: \operatorname{Homogeneous}\left(\right), (\forall root: \operatorname{PairRoot}\left(H\right), (\forall X: \operatorname{CompletionTree}\left(\right), ((\operatorname{rhoIterate}\left(a, X\right) = \operatorname{eval}\left(H, X\right)) \iff ((X = \operatorname{Omega}\left(\right)) \lor ((\operatorname{eval}\left(H, \operatorname{leafTrue}\left(\right)\right) = \operatorname{atomic}\left(a\right)) \land (\exists c: Nat, (X = \operatorname{atomic}\left(c\right)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/CompletionHomogeneousFixedPoints.completed_homogeneous_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CompletionTree is the unrestricted PFunctor.M for Boolean leaves and ordered binary nodes. The native substitution rho changes true leaves to false leaves, expands false leaves to a pair, and distributes through every node. The theorem quantifies over every natural exponent a, every finite homogeneous FreeMagma Nat expression H with an explicit pair root, and every completed tree X. No finiteness, regularity, computability, or ground term is assumed for X.

The finite branch uses the existing native mass and atomic-rank infrastructure. A positive-mass finite source cannot satisfy a pair-root feedback equation because the pair strictly increases mass; mass zero is exactly an atomic iterate. The existing completed injectivity of rho cancels the common atomic iterate, leaving precisely the test eval H (leaf true) = atomic a. Thus, when the test holds, every atomic iterate is a solution, and when it fails none is.

For an infinite solution with a leaf, a frontier occurrence below a is transported back to an actually reached original subtree. The new infinite_feedback_descent relation recovers an infinite original Y, records the exact shifted iterate X = rho^(a-b) Y, and proves that Y satisfies the same feedback equation. Repeating this descent yields arbitrarily large shifts while the leaf remains present; the existing full-prefix argument then forces an impossible unbounded finite leaf depth. The remaining infinite solution is therefore the unique leafless tree Omega.

The reverse directions are constructive: Omega is fixed by every iterate and every homogeneous pair expression, while each atomic iterate satisfies the equation whenever the alpha test holds by iterate commutation and homogeneity. PairRoot records the one-residual syntax boundary, excluding a lone residual, ground terms, and a second independent residual. The result formalizes the complete Theorem 2.3 split and its finite-solution consequence inside the unrestricted completed domain; it claims no external literature novelty.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/CompletionHomogeneousFixedPoints.completed_homogeneous_split`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionSupportClosure](NativeCompletionSupportClosure.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeRankedEqualityCompiler](NativeRankedEqualityCompiler.md)
