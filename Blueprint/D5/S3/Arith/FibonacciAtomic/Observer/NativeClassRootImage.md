# Native Class Root Images

## Abstract

Exact image filling and the finite class-root chart on complete native fibers.

Trees are all nonempty finite ordered Boolean trees. Alpha is the true leaf and beta the false leaf. The original substitution rho sends alpha to beta and beta to pair(beta,alpha), and preserves ordered pairing. A literal row C retains the concrete exterior and all occurrences of shared class names. D=Classes(C) is the finite subtype of appearing Nat labels; raw label gaps and unused Nat labels add no classes.

**Theorem 1.1 (Exact Literal Leaf Evaluation).**

$$\forall C: LiteralRow, (\forall f: \operatorname{Valuation}\left(Nat, Source\right), (\forall b: Bool, ((\operatorname{evaluateRow}\left(f, C\right) = \operatorname{of}\left(b\right)) \iff (\operatorname{lit}\left(\operatorname{RootTypeCompose}\left(f\right), b, C\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.evaluate_leaf` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every exterior C, arbitrary valuation f and Boolean leaf b, evaluating C yields exactly b if and only if C is a literal b under the roots of f. The full predecessor factorization uses this criterion at visible sibling roots.

**Theorem 1.2 (Roots of Extended Valuations).**

$$\forall C: LiteralRow, (\forall v: \operatorname{Valuation}\left(\operatorname{Classes}\left(C\right), Source\right), (\operatorname{RootExtend}\left(C, v\right) = \operatorname{typeExtend}\left(C, \operatorname{types}\left(C, v\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.root_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RootExtend(C,v) abbreviates the function n to rootType(extend(C,v,n)). Its equality with typeExtend(C,types(C,v)) holds on all natural labels, including the off-support alpha default. This identity connects literal evaluation to the finite root assignment.

**Definition 1.3 (Three Reached Root Types).**

$$\forall z: Source, (\operatorname{rootType}\left(z\right) = \operatorname{leafLabel}\left(z, empty\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.rootType` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Root types are some(true)=alpha, some(false)=beta and none=branch. The empty address is always reached, so there is no absent type.

**Definition 1.4 (Actual Substitution Image).**

$$\forall z: Source, ((\operatorname{Image}\left(z\right)) \iff (\exists u: Source, (\operatorname{rho}\left(u\right) = z)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.Image` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Image membership requires an actual finite predecessor under the original substitution rho.

**Definition 1.5 (Literal Leaf Predicate).**

$$\forall theta: Nat \to \operatorname{Option}\left(Bool\right), (\forall b: Bool, ((\forall c: Bool, ((\operatorname{lit}\left(theta, b, \operatorname{leaf}\left(c\right)\right)) \iff (c = b))) \land (\forall n: Nat, ((\operatorname{lit}\left(theta, b, \operatorname{hole}\left(n\right)\right)) \iff (\operatorname{theta}\left(n\right) = \operatorname{some}\left(b\right)))) \land (\forall e: LiteralRow, (\forall g: LiteralRow, (\neg (\operatorname{lit}\left(theta, b, \operatorname{pair}\left(e, g\right)\right)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.lit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A visible pair is never a literal leaf. A class name is a literal leaf exactly when its shared root type is that leaf.

**Definition 1.6 (Finite Recursive Image Predicate).**

$$\forall theta: Nat \to \operatorname{Option}\left(Bool\right), ((\neg (\operatorname{im}\left(theta, alpha\right))) \land (\operatorname{im}\left(theta, beta\right)) \land (\forall n: Nat, ((\operatorname{im}\left(theta, \operatorname{hole}\left(n\right)\right)) \iff (\neg (\operatorname{theta}\left(n\right) = alphaType)))) \land (\forall e: LiteralRow, (\forall g: LiteralRow, ((\operatorname{im}\left(theta, \operatorname{pair}\left(e, g\right)\right)) \iff (((\operatorname{lit}\left(theta, false, e\right)) \land (\operatorname{lit}\left(theta, true, g\right))) \lor ((\operatorname{im}\left(theta, e\right)) \land (\operatorname{im}\left(theta, g\right))))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.im` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

AlphaType means some(true). The first pair disjunct is exactly E=pair(beta,alpha); the second is a pair of images. This is the complete NBP.10.4 recursion.

**Definition 1.7 (Actual Branch Image Obligations).**

$$\forall C: LiteralRow, (\forall f: Nat \to Source, ((\operatorname{BranchImages}\left(C, f\right)) \iff (\forall n: Nat, ((\operatorname{member}\left(n, \operatorname{labels}\left(C\right)\right)) \implies ((\operatorname{rootType}\left(\operatorname{f}\left(n\right)\right) = none) \implies (\operatorname{Image}\left(\operatorname{f}\left(n\right)\right)))))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.BranchImages` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only appearing branch-valued classes require actual image membership. An alpha-valued class is allowed in the right child of E.

**Theorem 1.8 (Exact Test for Every Actual Filling).**

$$\forall C: LiteralRow, (\forall f: Nat \to Source, ((\operatorname{Image}\left(\operatorname{evaluateRow}\left(f, C\right)\right)) \iff ((\operatorname{BranchImages}\left(C, f\right)) \land (\operatorname{im}\left(\operatorname{rootTypeCompose}\left(f\right), C\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.filling_image_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

RootTypeCompose(f) maps n to rootType(f(n)). Structural induction proves the test for every literal row and every actual valuation. In the exceptional pair case both evaluated children are leaves, so their branch obligations are vacuous. For any legal x on D, put f=extend(C,x); the displayed statement becomes exactly NBP.10.6. A feasible branch type at a root hole does not make pair(alpha,alpha) an image: actual branch membership is required.

**Definition 1.9 (Type Assignment on Appearing Labels).**

$$\forall C: LiteralRow, (\forall theta: \operatorname{Classes}\left(C\right) \to \operatorname{Option}\left(Bool\right), (\forall n: Nat, (((\operatorname{member}\left(n, \operatorname{labels}\left(C\right)\right)) \implies (\operatorname{typeExtend}\left(C, theta, n\right) = \operatorname{theta}\left(n\right))) \land ((\neg (\operatorname{member}\left(n, \operatorname{labels}\left(C\right)\right))) \implies (\operatorname{typeExtend}\left(C, theta, n\right) = alphaType)))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.typeExtend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the appearing support n denotes its subtype element. Off-support defaults never create extra classes.

**Definition 1.10 (Roots of Class Values).**

$$\forall C: LiteralRow, (\forall x: \operatorname{Classes}\left(C\right) \to Source, (\forall d: \operatorname{Classes}\left(C\right), (\operatorname{types}\left(C, x, d\right) = \operatorname{rootType}\left(\operatorname{x}\left(d\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.types` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The map records the root of every actual appearing class value, with the same value at all repeated occurrences.

**Definition 1.11 (Exact Finite Feasible Chart).**

$$\forall C: LiteralRow, (\forall theta: \operatorname{Classes}\left(C\right) \to \operatorname{Option}\left(Bool\right), ((\operatorname{Admissible}\left(C, theta\right)) \iff ((\operatorname{im}\left(\operatorname{typeExtend}\left(C, theta\right), C\right)) \land (\operatorname{card}\left(\operatorname{leafClasses}\left(theta, true\right)\right) \leq 1) \land (\operatorname{card}\left(\operatorname{leafClasses}\left(theta, false\right)\right) \leq 1))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.Admissible` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

LeafClasses(theta,b) is the subset of D with theta(d)=some(b). The bounds count distinct classes, not occurrences. Admissible is precisely membership in Theta of NBP.10.5.

**Definition 1.12 (Full Actual One-Image Fiber).**

$$\forall P: CutSet, (\forall C: LiteralRow, (\operatorname{OriginFiber}\left(P, C\right) = \{u: Source \Vert \operatorname{canonicalRow}\left(P, \operatorname{rho}\left(u\right)\right) = C\}))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.OriginFiber` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is U in NBP.10.2. In the realization theorem C is an actual complete canonical row. Every concrete exterior constructor, repeated occurrence, distinct-class disequality and absent-cut strict-prefix blocking leaf remains. Empty and root cuts, blocked members, zero classes and all finite source sizes are included, without rank or history bounds.

**Definition 1.13 (Legal Image Fillings).**

$$\forall C: LiteralRow, (\operatorname{ImageValues}\left(C\right) = \{x: \operatorname{LegalValues}\left(C\right) \Vert \operatorname{Image}\left(\operatorname{evaluateRow}\left(\operatorname{extend}\left(C, x\right), C\right)\right)\})$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.ImageValues` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is X in NBP.10.1: all injective valuations on D whose filled complete exterior is an actual image.

**Definition 1.14 (Exact Image-Valuation and Origin Bijection).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall t0: Source, (\operatorname{Equiv}\left(\operatorname{ImageValues}\left(\operatorname{canonicalRow}\left(P, t0\right)\right), \operatorname{OriginFiber}\left(P, \operatorname{canonicalRow}\left(P, t0\right)\right)\right))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.imageOriginEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map is x to delta(evaluateRow(extend(C,x),C)), where delta is the original unique inverse on rho[Source]. The inverse recovers the class subtrees of rho(u) using their canonical representatives. The exact legal-row equivalence and both inverse laws give the NBP.10.3 bijection.

**Theorem 1.15 (Exact Types Attained Throughout the Actual Fiber).**

$$\forall P: CutSet, ((\operatorname{CutPrefixFree}\left(P\right)) \implies (\forall t0: Source, (\forall theta: \operatorname{Classes}\left(\operatorname{canonicalRow}\left(P, t0\right)\right) \to \operatorname{Option}\left(Bool\right), ((\operatorname{Admissible}\left(\operatorname{canonicalRow}\left(P, t0\right), theta\right)) \iff (\exists u: \operatorname{OriginFiber}\left(P, \operatorname{canonicalRow}\left(P, t0\right)\right), (\operatorname{types}\left(\operatorname{canonicalRow}\left(P, t0\right), \operatorname{recover}\left(P, \operatorname{rho}\left(u\right)\right)\right) = theta))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.class_root_chart` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Recover(P,rho(u)) abbreviates the legal valuation recovered in the complete row C=canonicalRow(P,t0), with the prefix-free proof supplied. This is exact NBP.10.7 on the entire actual NBP.10.2 domain. Enumerate the finite subtype D through e:D equivalent to Fin(card D). Leaf classes receive their forced leaves. Branch class d receives rho(pair(code(card D,e(d)),alpha)); these are images with branch roots, pairwise distinct by code and substitution injectivity, and distinct from both leaves. The cardinality bounds give full injectivity, and the recursive test gives image membership. The image-origin bijection realizes the assignment. Conversely, any origin recovers an injective image valuation; injectivity allows at most one class at each leaf. The construction includes zero branch classes and zero classes.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.Admissible`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.BranchImages`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.Image`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.ImageValues`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.OriginFiber`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.class_root_chart`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.evaluate_leaf`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.filling_image_iff`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.im`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.imageOriginEquiv`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.lit`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.rootType`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.root_extend`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.typeExtend`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Observer/NativeClassRootImage.types`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Observer/NativeCutFibers](NativeCutFibers.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates](../SourceCoordinates/IntrinsicSubstitutionCoordinates.md)
