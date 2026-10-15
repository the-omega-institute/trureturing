# Native Class Root Padding

## Abstract

Finite image padding realizes every feasible class-root assignment with exact bounded native replies.

Sources are all finite nonempty ordered Boolean trees. The substitution rho sends alpha to beta, sends beta to pair(beta,alpha), and preserves pairing. For a prefix-free finite cut P and a source t0, write C=canonicalRow(P,t0). Its occurring class set D=Classes(C) identifies repeated holes. ImageValues(C) consists of injective class valuations whose complete filling is an actual rho image; OriginFiber(P,C) consists of all finite origins with complete current row C. No source-size bound is imposed.

**Definition 1.1 (Reached Constructor Reply).**

$$(\operatorname{rootReply}\left(\operatorname{some}\left(true\right)\right) = alpha) \land (\operatorname{rootReply}\left(\operatorname{some}\left(false\right)\right) = beta) \land (\operatorname{rootReply}\left(none\right) = branch)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding.rootReply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The three root types some(true), some(false), and none mean alpha, beta, and branch respectively. An actual class root is reached, so it has no absent type.

**Definition 1.2 (Exterior and First-Class Query Rule).**

$$\forall theta: Nat \to \operatorname{Option}\left(Bool\right), ((\forall a: Address, (\forall b: Bool, (\operatorname{queryReply}\left(theta, a, \operatorname{leaf}\left(b\right)\right) = \operatorname{readout}\left(a, \operatorname{leaf}\left(b\right)\right)))) \land (\forall d: Nat, (\operatorname{queryReply}\left(theta, empty, \operatorname{hole}\left(d\right)\right) = \operatorname{rootReply}\left(\operatorname{theta}\left(d\right)\right))) \land (\forall d: Nat, (\forall a: Address, ((\neg (a = empty)) \implies (((\operatorname{theta}\left(d\right) = none) \implies (\operatorname{queryReply}\left(theta, a, \operatorname{hole}\left(d\right)\right) = branch)) \land ((\neg (\operatorname{theta}\left(d\right) = none)) \implies (\operatorname{queryReply}\left(theta, a, \operatorname{hole}\left(d\right)\right) = absent)))))) \land (\forall l: LiteralRow, (\forall r: LiteralRow, ((\operatorname{queryReply}\left(theta, empty, \operatorname{pair}\left(l, r\right)\right) = branch) \land (\forall a: Address, ((\operatorname{queryReply}\left(theta, \operatorname{left}\left(a\right), \operatorname{pair}\left(l, r\right)\right) = \operatorname{queryReply}\left(theta, a, l\right)) \land (\operatorname{queryReply}\left(theta, \operatorname{right}\left(a\right), \operatorname{pair}\left(l, r\right)\right) = \operatorname{queryReply}\left(theta, a, r\right))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding.queryReply` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Follow the fixed exterior until a concrete reply or a class hole is encountered. Only that one class type is inspected. An empty suffix returns its constructor. A nonempty suffix returns absent for either leaf type and branch for a branch type. Thus concrete blocking leaves, absent addresses, root holes and repeated-class occurrences are included.

**Definition 1.3 (Inclusive Branch Depth).**

$$\forall C: LiteralRow, (\forall L: Nat, (\forall v: \operatorname{Classes}\left(C\right) \to Source, ((\operatorname{DeepValues}\left(C, L, v\right)) \iff (\forall d: \operatorname{Classes}\left(C\right), ((\operatorname{rootType}\left(\operatorname{v}\left(d\right)\right) = none) \implies (\forall a: Address, ((\operatorname{length}\left(a\right) \leq L) \implies (\operatorname{readout}\left(a, \operatorname{v}\left(d\right)\right) = branch))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding.DeepValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every address of length at most L inside a branch-valued class returns branch. In particular no such class has a leaf at depth at most L; its minimum native leaf depth is strictly greater than L.

**Theorem 1.4 (Simultaneous Actual Padding and Query Correspondence).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall t0: Source, (\forall L: Nat, (\forall theta: \operatorname{Classes}\left(\operatorname{canonicalRow}\left(P, t0\right)\right) \to \operatorname{Option}\left(Bool\right), ((\operatorname{Admissible}\left(\operatorname{canonicalRow}\left(P, t0\right), theta\right)) \implies (\exists v: \operatorname{ImageValues}\left(\operatorname{canonicalRow}\left(P, t0\right)\right), (\exists u: \operatorname{OriginFiber}\left(P, \operatorname{canonicalRow}\left(P, t0\right)\right), ((\operatorname{rho}\left(u\right) = \operatorname{evaluateRow}\left(\operatorname{extend}\left(\operatorname{canonicalRow}\left(P, t0\right), v\right), \operatorname{canonicalRow}\left(P, t0\right)\right)) \land (\operatorname{types}\left(\operatorname{canonicalRow}\left(P, t0\right), v\right) = theta) \land (\operatorname{DeepValues}\left(\operatorname{canonicalRow}\left(P, t0\right), L, v\right)) \land (\forall a: Address, ((\operatorname{length}\left(a\right) \leq L) \implies (\operatorname{readout}\left(a, \operatorname{rho}\left(u\right)\right) = \operatorname{queryReply}\left(\operatorname{typeExtend}\left(\operatorname{canonicalRow}\left(P, t0\right), theta\right), a, \operatorname{canonicalRow}\left(P, t0\right)\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding.padded_native_query_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each admissible assignment theta, one finite valuation and one actual origin satisfy all displayed conclusions together. Different classes remain distinct and every repeated occurrence uses its class value. Branch classes receive distinct image codes duplicated into complete binary trees of depth L+1. Duplication preserves injectivity and image membership; induction on addresses proves the branch-depth bound. Leaf classes receive their forced literals, whose multiplicity bounds ensure injectivity across the entire valuation. The exact image grammar and legal-row theorem give the original finite origin. Structural induction through the exterior then gives every bounded native reply on this same image. Choosing these valuations for all admissible theta gives the simultaneous family, including zero classes and zero branch classes. No cross-origin distinction is required. The chosen finite origins are representatives, not a reconstruction of every source. The result supplies no acquisition permission, runtime query extraction, physical operation or controller-state bound.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding.DeepValues`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding.padded_native_query_chart`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding.queryReply`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootPadding.rootReply`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage](NativeClassRootImage.md)
