# Integral Euler frequency identities

## Abstract

Integral Euler derivatives admit finite odd-length frequency formulas.

All indices and exponents are natural numbers. A is integer-valued; F and exp are rational formal power series. C embeds constants. The residue function casts an integer or natural value to ZMod of its first argument. All arithmetic inside a residue identity is in that ring. Young supplies the prior ordinary congruence component; the finite derivation here proves the integral identities directly.

**Definition 1.1 (Integral derivatives).**

$$\forall b: \mathbb{N}, ((\operatorname{A}\left(b, 0\right) = 1) \land (\forall n: \mathbb{N}, (\operatorname{A}\left(b, n + 1\right) = b^{n + 1} - \sum_{i \in \operatorname{range}\left(n + 1\right)} (\operatorname{choose}\left(n + 1, i\right) \cdot 2^{n - i} \cdot \operatorname{A}\left(b, i\right)))))$$

*Formalization.* `D5/S1/Recurrence/Periodic/EulerSignedFrequency.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer recurrence constructs every derivative before modular reduction. Natural binomial coefficients and b are cast to the integers.

**Definition 1.2 (The signed exponential series).**

$$\forall b: \mathbb{N}, (\operatorname{F}\left(b\right) = \sum_{n \in \mathbb{N}} (\frac{\operatorname{A}\left(b, n\right) \cdot X^{n}}{\operatorname{factorial}\left(n\right)}))$$

*Formalization.* `D5/S1/Recurrence/Periodic/EulerSignedFrequency.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

X is the distinguished formal indeterminate. The integer coefficients A are embedded in the rationals; no factorial is inverted in a residue ring.

**Theorem 1.3 (The exact exponential identity).**

$$\forall b: \mathbb{N}, (\left(1 + \operatorname{exp}\left(\mathbb{Q}\right)^{2}\right) \cdot \operatorname{F}\left(b\right) = \operatorname{C}\left(2\right) \cdot \operatorname{exp}\left(\mathbb{Q}\right)^{b})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerSignedFrequency.generating_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factorial-normalized coefficient comparison reduces the identity to the integral recurrence.

**Theorem 1.4 (The finite odd-length identity).**

$$\forall b: \mathbb{N}, (\forall L: \mathbb{N}, ((\operatorname{Odd}\left(L\right)) \implies (\left(1 + \operatorname{exp}\left(\mathbb{Q}\right)^{2 \cdot L}\right) \cdot \operatorname{F}\left(b\right) = \operatorname{C}\left(2\right) \cdot \sum_{h \in \operatorname{range}\left(L\right)} (\operatorname{C}\left((-1)^{h}\right) \cdot \operatorname{exp}\left(\mathbb{Q}\right)^{2 \cdot h + b}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerSignedFrequency.finite_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alternating geometric sum has numerator one plus the Lth power exactly when L is odd.

**Theorem 1.5 (The signed branch equations).**

$$(\operatorname{derivative}\left(\operatorname{F}\left(0\right)\right) = \operatorname{F}\left(0\right) \cdot \left(\operatorname{F}\left(0\right) - 2\right)) \land ((\operatorname{derivative}\left(\operatorname{F}\left(1\right)\right) = \operatorname{F}\left(1\right) \cdot \left(\operatorname{F}\left(0\right) - 1\right)) \land (\operatorname{F}\left(1\right)^{2} = \operatorname{F}\left(0\right) \cdot \left(2 - \operatorname{F}\left(0\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerSignedFrequency.branch_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiation and cancellation of the nonzero exponential denominator prove both differential equations and the quadratic relation.

**Theorem 1.6 (Integral finite moments modulo an odd modulus).**

$$\forall b: \mathbb{N}, (\forall L: \mathbb{N}, (\forall u: \mathbb{N}, (\forall q: \mathbb{N}, (\forall j: \mathbb{N}, ((\operatorname{Odd}\left(L\right)) \implies ((\operatorname{Odd}\left(q\right)) \implies ((q \mid u \cdot L) \implies (\operatorname{residue}\left(q, u\right)^{j} \cdot \operatorname{residue}\left(q, \operatorname{A}\left(b, j\right)\right) = \sum_{h \in \operatorname{range}\left(L\right)} (\operatorname{residue}\left(q, (-1)\right)^{h} \cdot \operatorname{residue}\left(q, u \cdot \left(2 \cdot h + b\right)\right)^{j})))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerSignedFrequency.scaled_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive-order exponential derivatives contain the modulus. The remaining factor two is cancelled using oddness of q. This includes j=0.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/EulerSignedFrequency.A`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerSignedFrequency.F`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerSignedFrequency.branch_equations`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerSignedFrequency.finite_identity`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerSignedFrequency.generating_identity`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerSignedFrequency.scaled_moment`
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFFixedPoint](../Residue/QuarticEGFFixedPoint.md)
