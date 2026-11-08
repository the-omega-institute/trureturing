# Loop-zero matching monoid

## Abstract

Loop-zero matching monoid

None is the absorbing zero; some(d) is a literal fixed-point-free boundary involution. Multiplication is some(composite(d,e)) when the internal loop count is zero and is none otherwise. The unit is the identity through-strand matching. These definitions include zero strands.

**Definition 1.1 (ZeroMatching).**

$$\forall n \in Nat,\; \operatorname{ZeroMatching}\left(n\right) = \operatorname{Option}\left(\operatorname{Matching}\left(\operatorname{Boundary}\left(n\right)\right)\right)$$

*Formalization.* `D5/S3/Topology/BrauerZeroMonoid.ZeroMatching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The carrier adjoins one absorbing zero to all matchings.

**Definition 1.2 (zeroMatchingMonoid).**

$$\forall n \in Nat,\; \operatorname{zeroMatchingMonoid}\left(n\right) = \operatorname{MonoidWithZeroStructure}\left(\operatorname{ZeroMatching}\left(n\right), \operatorname{LoopZeroProduct}\left(n\right), \operatorname{Some}\left(\operatorname{identityMatching}\left(n\right)\right), None\right)$$

*Formalization.* `D5/S3/Topology/BrauerZeroMonoid.zeroMatchingMonoid` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The product has the displayed loop test. Pairing associativity and the loop cocycle prove associativity; the identity creates no internal loops.

**Theorem 1.3 (some_mul_some).**

$$\forall N \in Nat,\; \forall d \in \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right),\; \forall e \in \operatorname{Matching}\left(\operatorname{Boundary}\left(N\right)\right),\; \operatorname{Multiply}\left(\operatorname{Some}\left(d\right), \operatorname{Some}\left(e\right)\right) = \operatorname{If}\left(\operatorname{internalLoopCount}\left(d, e\right) = 0, \operatorname{Some}\left(\operatorname{composite}\left(d, e\right)\right), None\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/BrauerZeroMonoid.some_mul_some` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed product is the MonoidWithZero multiplication, not an additional operation.

## References

- Truth anchor: `D5/S3/Topology/BrauerZeroMonoid.ZeroMatching`
- Truth anchor: `D5/S3/Topology/BrauerZeroMonoid.some_mul_some`
- Truth anchor: `D5/S3/Topology/BrauerZeroMonoid.zeroMatchingMonoid`
- Dependency: [D5/S3/Topology/FiniteMatchingAssociativity](FiniteMatchingAssociativity.md)
- Dependency: [D5/S3/Topology/FiniteMatchingClosure](FiniteMatchingClosure.md)
- Dependency: [D5/S3/Topology/FiniteMatchingComposition](FiniteMatchingComposition.md)
- Dependency: [D5/S3/Topology/FiniteMatchingSewing](FiniteMatchingSewing.md)
