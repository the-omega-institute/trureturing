# Strict Suffixes and Conditional Path Sums

## Abstract

The actual boundary path sum splits at every finite original prefix, for every square summable increment vector, in the common suffix L2 space.

**Definition 1.1 (descendant).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.descendant`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.descendant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Appending a nonempty suffix to p gives a nonempty original edge. This address map is injective.

**Definition 1.2 (S).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.S`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.S` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The suffix operator has coordinate S(p)z at u equal to z at p appended to u. Only nonempty u occur, so the edge p and its ancestors are excluded. Injective restriction of the square summable coordinates gives a contraction on the original H.

**Definition 1.3 (prefixes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.prefixes`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.prefixes` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite set consists of the nonempty original prefixes of p. It includes p when p is nonempty and is empty when p is empty.

**Definition 1.4 (prefixSum).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.prefixSum`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.prefixSum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The prefix functional sums the original increment coordinates over this finite set. It is continuous because every coordinate evaluation is continuous.

**Definition 1.5 (constG).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.constG`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.constG` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous constant embedding sends c to the actual constant function c in the same L2(M) that contains Jz.

**Theorem 1.6 (The All Vector Path Split).**

$$(\forall p: \operatorname{Address}\left(\right), (\forall z: \operatorname{H}\left(\right), (\forall u: \operatorname{Edge}\left(\right), (\operatorname{S}\left(p, z, u\right)=\operatorname{apply}\left(z, \operatorname{descendant}\left(p, u\right)\right)))))\land(\forall p: \operatorname{Address}\left(\right), (\forall z: \operatorname{H}\left(\right), (\Vert \operatorname{S}\left(p, z\right) \Vert\leq\Vert z \Vert)))\land(\forall p: \operatorname{Address}\left(\right), (\forall z: \operatorname{H}\left(\right), (\operatorname{prefixSum}\left(p, z\right)=\operatorname{sum}\left(\operatorname{prefixes}\left(p\right), z\right))))\land(\forall c: \mathbb{R}, (\operatorname{aeEq}\left(M, \operatorname{constG}\left(c\right), \operatorname{constant}\left(c\right)\right)))\land(\forall p: \operatorname{Address}\left(\right), (\forall z: \operatorname{H}\left(\right), (\operatorname{pullback}\left(p, \operatorname{J}\left(z\right)\right)=\operatorname{constG}\left(\operatorname{prefixSum}\left(p, z\right)\right)+\operatorname{J}\left(\operatorname{S}\left(p, z\right)\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.boundary_path_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite p and every z in the original H, the conditional pullback of Jz equals the constant finite prefix sum plus J applied to the strict suffix vector. The equality is in the original suffix L2(M). The pullback uses the actual normalized restricted law; no ambient measure preservation is imposed on prepend.

On a single increment at q, a prefix q of p contributes the constant increment. A strict descendant q of p contributes precisely the indicator of its nonempty suffix cylinder. Incomparable addresses contribute zero. These alternatives follow from the original address coordinates and include equality q=p in the prefix case.

The identity on single increments extends by continuity of the pullback, J, the finite prefix functional and the suffix contraction. Continuous linear maps on ell2 are determined by the single increments, so this proves the identity for every square summable z. No finite support restriction remains, and an empty p gives a zero prefix sum and the unchanged suffix vector.

The centered mass stopping projection and its weighted residual norm formula require additional results. No spectral operator, covariance or eigenvalue counting assertion is made here.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.S`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.boundary_path_split`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.constG`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.descendant`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.prefixSum`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryPathSplit.prefixes`
- Dependency: [D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryConditionalLaw](BiasedBoundaryConditionalLaw.md)
