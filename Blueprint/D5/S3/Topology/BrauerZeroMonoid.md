# Loop-zero matching monoid

## Abstract

Loop-zero matching monoid

Option.none is an absorbing zero. Option.some d retains the literal boundary matching d. The product follows the sewn paths when there is no internal loop, and is zero when a loop occurs. These definitions include zero strands.

**Definition 1.1 (ZeroMatching).**

$$\forall (N: \operatorname{Nat}), (\operatorname{ZeroMatching}\left(N\right) = \operatorname{Option}\left(\operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right)\right))$$

*Formalization.* `D5/S3/Topology/BrauerZeroMonoid.ZeroMatching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier adjoins a single zero to the set of matchings.

**Definition 1.2 (zeroMatchingMonoid).**

$$\forall (N: \operatorname{Nat}), ((((1: \operatorname{ZeroMatching}\left(N\right)) = \operatorname{Option}.\operatorname{some}\left(\operatorname{identityMatching}\left(N\right)\right)) \land ((0: \operatorname{ZeroMatching}\left(N\right)) = \operatorname{Option}.\operatorname{none})) \land (\forall (a: \operatorname{ZeroMatching}\left(N\right)), (\forall (b: \operatorname{ZeroMatching}\left(N\right)), (((a) \cdot (b) = \operatorname{multiply}\left(a, b\right)) \land (\operatorname{multiply}\left(a, b\right) = \operatorname{Option}.\operatorname{casesOn}\left(a, \operatorname{Option}.\operatorname{none}, ((d: \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right)) \mapsto \operatorname{Option}.\operatorname{casesOn}\left(b, \operatorname{Option}.\operatorname{none}, ((e: \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right)) \mapsto \operatorname{ite}\left(\operatorname{internalLoopCount}\left(d, e\right) = 0, \operatorname{Option}.\operatorname{some}\left(\operatorname{composite}\left(d, e\right)\right), \operatorname{Option}.\operatorname{none}\right))\right))\right))))))$$

*Formalization.* `D5/S3/Topology/BrauerZeroMonoid.zeroMatchingMonoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

These are the literal one, zero and mul fields of zeroMatchingMonoid. Its associativity field is multiply_assoc; the unit laws use composite_left_identity, composite_right_identity and the corresponding zero loop counts. Option.casesOn expands the literal private multiply pattern match. The zero_mul and mul_zero fields are multiply_none_left and multiply_none_right.

**Theorem 1.3 (some_mul_some).**

$$\forall (N: \operatorname{Nat}), (\forall (d: \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right)), (\forall (e: \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right)), (((\operatorname{Option}.\operatorname{some}\left(d\right): \operatorname{ZeroMatching}\left(N\right))) \cdot (\operatorname{Option}.\operatorname{some}\left(e\right)) = \operatorname{ite}\left(\operatorname{internalLoopCount}\left(d, e\right) = 0, \operatorname{Option}.\operatorname{some}\left(\operatorname{composite}\left(d, e\right)\right), \operatorname{Option}.\operatorname{none}\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/BrauerZeroMonoid.some_mul_some` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This is the multiplication of zeroMatchingMonoid.

## References

- Truth anchor: `D5/S3/Topology/BrauerZeroMonoid.ZeroMatching`
- Truth anchor: `D5/S3/Topology/BrauerZeroMonoid.some_mul_some`
- Truth anchor: `D5/S3/Topology/BrauerZeroMonoid.zeroMatchingMonoid`
- Dependency: [D5/S3/Topology/FiniteMatchingAssociativity](FiniteMatchingAssociativity.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](FiniteMatchingClosure.md)
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](FiniteMatchingComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingSewing](FiniteMatchingSewing.md)
