# Intrinsic Substitution Coordinates

## Abstract

Maximal actual substitution ancestry determines a unique primitive endpoint and the full ordered-pair law.

T is FreeMagma Bool, the actual nonempty finite ordered binary trees. Alpha is the true leaf and beta the false leaf. Pair(s,t) retains its literal ordered children and brackets. R(n,t) denotes the n-fold iterate of the original substitution rho, which sends alpha to beta and beta to pair(beta,alpha), and preserves ordered pairing. All exponents are natural numbers, including zero.

**Theorem 1.1 (Alpha has no predecessor).**

$$\forall t: T, \operatorname{R}\left(1, t\right) \neq alpha$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.no_alpha` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each substituted leaf is beta or the pair (beta,alpha), and each substituted internal node remains an internal node. Thus alpha is absent from the image.

**Theorem 1.2 (Exact Ordered Pair Image Grammar).**

$$\forall s: T, (\forall t: T, ((\exists x: T, (\operatorname{R}\left(1, x\right) = \operatorname{pair}\left(s, t\right))) \iff (((s = beta) \land (t = alpha)) \lor ((\exists x: T, (\operatorname{R}\left(1, x\right) = s)) \land (\exists y: T, (\operatorname{R}\left(1, y\right) = t))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.pair_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A substituted beta gives the special pair (beta,alpha). Every substituted compound gives a pair of substituted children. Conversely the alternatives have preimages beta and the ordered pair of the two child preimages.

**Definition 1.3 (Primitive endpoint).**

$$\forall p: T, ((\operatorname{Primitive}\left(p\right)) \iff (\neg (\exists x: T, (\operatorname{R}\left(1, x\right) = p))))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.Primitive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A primitive source has no actual one-step predecessor.

**Definition 1.4 (Actual substitution ancestors).**

$$\forall t: T, (\operatorname{Ancestors}\left(t\right) = \{(x, k) \Vert x:T, k:\operatorname{Nat}\left(\right), \operatorname{R}\left(k, x\right) = t\})$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.Ancestors` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Ancestors(t) retains every actual source and legal exponent. For this fixed t, the map (x,k) to (t,x,k) embeds it in the existing finite entrance fiber indexed by G(wd(t)). That geometry is only an internal index establishing finiteness; it identifies no source or primitive root.

**Definition 1.5 (Legal exponents).**

$$\forall t: T, (\operatorname{legalIndices}\left(t\right) = \{k \Vert k:\operatorname{Nat}\left(\right), \exists x: T, (\operatorname{R}\left(k, x\right) = t)\})$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.legalIndices` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set of actual legal exponents contains zero.

**Definition 1.6 (Maximal legal exponent).**

$$\forall t: T, (\operatorname{depth}\left(t\right) = \operatorname{max}\left(\operatorname{legalIndices}\left(t\right)\right))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.depth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Depth directly reuses Geometry.AncestorAreaInstability.depth, the supremum of the original legal-exponent set. Finiteness makes it the maximum displayed here. It is not address length or tree height.

**Definition 1.7 (Actual maximal ancestor).**

$$\forall t: T, (\operatorname{R}\left(\operatorname{depth}\left(t\right), \operatorname{root}\left(t\right)\right) = t)$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Root(t) is an actual ancestor at the maximum exponent. Injectivity makes it unique, and maximality excludes a further predecessor.

**Definition 1.8 (Alpha-ray flag).**

$$\forall t: T, ((\operatorname{flag}\left(t\right) = 1) \iff (\operatorname{root}\left(t\right) = alpha))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.flag` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Boolean flag is true exactly when the primitive endpoint is alpha. In formulas, Boolean true is written 1 and false is written 0.

**Definition 1.9 (Intrinsic coordinate).**

$$\forall t: T, (\operatorname{Q}\left(t\right) = (\operatorname{depth}\left(t\right), \operatorname{flag}\left(t\right)))$$

*Formalization.* `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate consists of intrinsic depth and the alpha-ray flag.

**Theorem 1.10 (Unique Primitive-Ray Coordinates).**

$$\forall t: T, ((\forall k: \operatorname{Nat}\left(\right), ((\exists x: T, (\operatorname{R}\left(k, x\right) = t)) \iff (k \leq \operatorname{depth}\left(t\right)))) \land (\operatorname{Primitive}\left(\operatorname{root}\left(t\right)\right)) \land (\operatorname{R}\left(\operatorname{depth}\left(t\right), \operatorname{root}\left(t\right)\right) = t) \land (\forall p: T, (\forall n: \operatorname{Nat}\left(\right), ((\operatorname{Primitive}\left(p\right)) \implies ((\operatorname{R}\left(n, p\right) = t) \implies ((n = \operatorname{depth}\left(t\right)) \land (p = \operatorname{root}\left(t\right))))))) \land ((\operatorname{flag}\left(t\right) = 1) \iff (\operatorname{R}\left(\operatorname{depth}\left(t\right), alpha\right) = t)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.intrinsic_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every legal exponent is at most the actual maximum. Conversely, for k at most the maximum, applying the remaining depth to the primitive endpoint constructs a k-step ancestor. A predecessor of the maximal ancestor would increase the maximum. If t=R(n,p) with p primitive, any deeper ancestor cancels the injective n-fold iterate to give a positive predecessor of p. Thus n is exactly the maximum and p is exactly root(t).

**Theorem 1.11 (Complete Substitution and Pairing Laws).**

$$(\forall t: T, ((\forall k: \operatorname{Nat}\left(\right), ((\exists x: T, (\operatorname{R}\left(k, x\right) = t)) \iff (k \leq \operatorname{depth}\left(t\right)))) \land (\operatorname{Primitive}\left(\operatorname{root}\left(t\right)\right)) \land (\operatorname{R}\left(\operatorname{depth}\left(t\right), \operatorname{root}\left(t\right)\right) = t) \land (\forall p: T, (\forall n: \operatorname{Nat}\left(\right), ((\operatorname{Primitive}\left(p\right)) \implies ((\operatorname{R}\left(n, p\right) = t) \implies ((n = \operatorname{depth}\left(t\right)) \land (p = \operatorname{root}\left(t\right))))))) \land ((\operatorname{flag}\left(t\right) = 1) \iff (\operatorname{R}\left(\operatorname{depth}\left(t\right), alpha\right) = t)))) \land (\forall t: T, (\operatorname{Q}\left(\operatorname{R}\left(1, t\right)\right) = (\operatorname{depth}\left(t\right) + 1, \operatorname{flag}\left(t\right)))) \land (\forall s: T, (\forall t: T, ((((\operatorname{flag}\left(s\right) = 1) \land (\operatorname{flag}\left(t\right) = 1) \land (\operatorname{depth}\left(s\right) = \operatorname{depth}\left(t\right) + 1)) \implies (\operatorname{Q}\left(\operatorname{pair}\left(s, t\right)\right) = (\operatorname{depth}\left(t\right) + 2, 1))) \land ((\neg ((\operatorname{flag}\left(s\right) = 1) \land (\operatorname{flag}\left(t\right) = 1) \land (\operatorname{depth}\left(s\right) = \operatorname{depth}\left(t\right) + 1))) \implies (\operatorname{Q}\left(\operatorname{pair}\left(s, t\right)\right) = (\operatorname{min}\left(\operatorname{depth}\left(s\right), \operatorname{depth}\left(t\right)\right), 0)))))) \land (\operatorname{Q}\left(alpha\right) = (0, 1)) \land (\operatorname{Q}\left(beta\right) = (1, 1))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.all_source_coordinate_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Substitution increases the intrinsic depth by one and preserves the primitive endpoint. For a pair with child depths a,b, remove m=min(a,b) common substitution steps. The residual children are R(a-m,root(s)) and R(b-m,root(t)). At least one is primitive. A pair lies in the one-step image precisely when it is (beta,alpha), or both children are images. The latter alternative is impossible for the residual pair.

The exceptional residual (beta,alpha) occurs exactly when both child flags are true and a=b+1. It is R(2,alpha), so the pair has coordinate (b+2,1). Otherwise the residual pair is itself primitive and cannot be the leaf alpha; its coordinate is (m,0). This applies to both leaves, zero depths, equal depths and arbitrary children off the alpha ray. No quotient, inverse geometry or acquisition bound is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.Ancestors`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.Primitive`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.Q`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.all_source_coordinate_law`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.depth`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.flag`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.intrinsic_coordinates`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.legalIndices`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.no_alpha`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.pair_image`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.root`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/AncestorAreaInstability](../Geometry/AncestorAreaInstability.md)
