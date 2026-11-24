# Exact transport to standard numbers

## Abstract

The one-way Layer 2 shadow of Omega arithmetic and its projective circle in Mathlib.

**Definition 1.1 (Natural-number shadow).**

Lean statement: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdNat`

*Formalization.* `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdNat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero constructor maps to zero, and a successor maps to the standard successor.

**Definition 1.2 (Integer shadow).**

Lean statement: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdInt`

*Formalization.* `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdInt` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Maps each nonnegative or negative-successor constructor to its standard counterpart.

**Definition 1.3 (Rational shadow).**

Lean statement: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat`

*Formalization.* `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A finite ratio maps to its signed numerator divided by its positive denominator. The undefined constructor maps to zero.

**Definition 1.4 (Real shadow).**

Lean statement: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toReal`

*Formalization.* `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toReal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The rational shadow followed by the canonical inclusion of the rationals in the reals.

**Theorem 1.5 (Transport of natural addition).**

$$\forall a \in OmegaNat, b \in OmegaNat,\; \operatorname{toStdNat}\left(a + b\right) = \operatorname{toStdNat}\left(a\right) + \operatorname{toStdNat}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdNat_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the right argument transports successors.

**Theorem 1.6 (Transport of natural multiplication).**

$$\forall a \in OmegaNat, b \in OmegaNat,\; \operatorname{toStdNat}\left(a \cdot b\right) = \operatorname{toStdNat}\left(a\right) \cdot \operatorname{toStdNat}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdNat_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on the right argument uses transport of natural addition.

**Theorem 1.7 (Transport of integer addition).**

$$\forall a \in OmegaInt, b \in OmegaInt,\; \operatorname{toStdInt}\left(a + b\right) = \operatorname{toStdInt}\left(a\right) + \operatorname{toStdInt}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdInt_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Mixed signs use transport of subtraction of two naturals.

**Theorem 1.8 (Transport of integer negation).**

$$\forall a \in OmegaInt,\; \operatorname{toStdInt}\left(-a\right) = -\operatorname{toStdInt}\left(a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdInt_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Negation exchanges the two sign branches except at zero.

**Theorem 1.9 (Transport of integer multiplication).**

$$\forall a \in OmegaInt, b \in OmegaInt,\; \operatorname{toStdInt}\left(a \cdot b\right) = \operatorname{toStdInt}\left(a\right) \cdot \operatorname{toStdInt}\left(b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdInt_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sign cases use transport of natural multiplication.

**Theorem 1.10 (Equivalent fractions have equal rational shadows).**

$$\forall x \in IntRatio, y \in IntRatio,\; \operatorname{Equivalent}\left(x, y\right) \Rightarrow \operatorname{toRat}\left(x\right) = \operatorname{toRat}\left(y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat_equivalent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For finite fractions, equality of cross products gives equality of rational readings.

**Theorem 1.11 (Transport of finite-ratio addition).**

$$\forall a \in OmegaInt, c \in OmegaInt, b \in OmegaNat, d \in OmegaNat,\; \operatorname{toRat}\left(\operatorname{fraction}\left(a, b\right) + \operatorname{fraction}\left(c, d\right)\right) = \operatorname{toRat}\left(\operatorname{fraction}\left(a, b\right)\right) + \operatorname{toRat}\left(\operatorname{fraction}\left(c, d\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat_add` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The denominator predecessors encode positive denominators. The addition uses their product as a common denominator.

**Theorem 1.12 (Transport of ratio multiplication).**

$$\forall x \in IntRatio, y \in IntRatio,\; \operatorname{toRat}\left(x \cdot y\right) = \operatorname{toRat}\left(x\right) \cdot \operatorname{toRat}\left(y\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite products multiply numerators and denominators. Undefined inputs give zero in the rational shadow.

**Theorem 1.13 (Transport of the reciprocal).**

$$\forall x \in IntRatio,\; \operatorname{toRat}\left(\operatorname{inv}\left(x\right)\right) = \operatorname{inv}\left(\operatorname{toRat}\left(x\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A nonzero finite ratio exchanges the magnitudes with the sign in the numerator. The inverse of zero has shadow zero.

**Theorem 1.14 (The real Cayley image has unit norm).**

$$\forall p \in OmegaInt, q \in OmegaInt,\; \operatorname{Nonzero}\left(p, q\right) \Rightarrow \operatorname{toReal}\left(\operatorname{X}\left(p, q\right)\right)^{2} + \operatorname{toReal}\left(\operatorname{Y}\left(p, q\right)\right)^{2} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.cayley_circle_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonzero pair has positive squared norm. Its strict circle identity transports first to the rationals and then to the reals.

**Theorem 1.15 (The real overlap is between zero and one).**

$$\forall p \in OmegaInt, q \in OmegaInt,\; 0 \le \operatorname{toReal}\left(\operatorname{kappa}\left(p, q\right)\right) \land \operatorname{toReal}\left(\operatorname{kappa}\left(p, q\right)\right) \le 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.kappa_unit_interval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At the origin the undefined overlap has shadow zero. Elsewhere positive denominators transport the signed cross-product inequalities to the rationals and then to the reals.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.cayley_circle_unit`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.kappa_unit_interval`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat_add`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat_equivalent`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat_inv`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toRat_mul`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toReal`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdInt`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdInt_add`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdInt_mul`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdInt_neg`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdNat`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdNat_add`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaShadowBridge.toStdNat_mul`
