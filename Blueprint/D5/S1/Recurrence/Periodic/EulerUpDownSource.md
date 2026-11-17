# The ordinary Euler source carrier

## Abstract

The source recurrence defines ordinary A000111 and proves both exact sign bridges.

Integral Euler derivatives admit finite odd-length frequency formulas.

All indices and exponents are natural numbers. A is integer-valued; F and exp are rational formal power series. C embeds constants. The residue function casts an integer or natural value to ZMod of its first argument. All arithmetic inside a residue identity is in that ring. Young supplies the prior ordinary congruence component; the finite derivation here proves the integral identities directly.

**Definition 1.1 (Integral derivatives).**

$$\forall b: \mathbb{N}, ((\operatorname{A}\left(b, 0\right) = 1) \land (\forall n: \mathbb{N}, (\operatorname{A}\left(b, n + 1\right) = b^{n + 1} - \sum_{i \in \operatorname{range}\left(n + 1\right)} (\operatorname{choose}\left(n + 1, i\right) \cdot 2^{n - i} \cdot \operatorname{A}\left(b, i\right)))))$$

*Formalization.* `D5/S1/Recurrence/Periodic/EulerUpDownSource.A` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The integer recurrence constructs every derivative before modular reduction. Natural binomial coefficients and b are cast to the integers.

**Definition 1.2 (The signed exponential series).**

$$\forall b: \mathbb{N}, (\operatorname{F}\left(b\right) = \sum_{n \in \mathbb{N}} (\frac{\operatorname{A}\left(b, n\right) \cdot X^{n}}{\operatorname{factorial}\left(n\right)}))$$

*Formalization.* `D5/S1/Recurrence/Periodic/EulerUpDownSource.F` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

X is the distinguished formal indeterminate. The integer coefficients A are embedded in the rationals; no factorial is inverted in a residue ring.

**Theorem 1.3 (The exact exponential identity).**

$$\forall b: \mathbb{N}, (\left(1 + \operatorname{exp}\left(\mathbb{Q}\right)^{2}\right) \cdot \operatorname{F}\left(b\right) = \operatorname{C}\left(2\right) \cdot \operatorname{exp}\left(\mathbb{Q}\right)^{b})$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerUpDownSource.generating_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factorial-normalized coefficient comparison reduces the identity to the integral recurrence.

**Theorem 1.4 (The finite odd-length identity).**

$$\forall b: \mathbb{N}, (\forall L: \mathbb{N}, ((\operatorname{Odd}\left(L\right)) \implies (\left(1 + \operatorname{exp}\left(\mathbb{Q}\right)^{2 \cdot L}\right) \cdot \operatorname{F}\left(b\right) = \operatorname{C}\left(2\right) \cdot \sum_{h \in \operatorname{range}\left(L\right)} (\operatorname{C}\left((-1)^{h}\right) \cdot \operatorname{exp}\left(\mathbb{Q}\right)^{2 \cdot h + b}))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerUpDownSource.finite_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The alternating geometric sum has numerator one plus the Lth power exactly when L is odd.

**Theorem 1.5 (The signed branch equations).**

$$(\operatorname{derivative}\left(\operatorname{F}\left(0\right)\right) = \operatorname{F}\left(0\right) \cdot \left(\operatorname{F}\left(0\right) - 2\right)) \land ((\operatorname{derivative}\left(\operatorname{F}\left(1\right)\right) = \operatorname{F}\left(1\right) \cdot \left(\operatorname{F}\left(0\right) - 1\right)) \land (\operatorname{F}\left(1\right)^{2} = \operatorname{F}\left(0\right) \cdot \left(2 - \operatorname{F}\left(0\right)\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerUpDownSource.branch_equations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Differentiation and cancellation of the nonzero exponential denominator prove both differential equations and the quadratic relation.

**Theorem 1.6 (Integral finite moments modulo an odd modulus).**

$$\forall b: \mathbb{N}, (\forall L: \mathbb{N}, (\forall u: \mathbb{N}, (\forall q: \mathbb{N}, (\forall j: \mathbb{N}, ((\operatorname{Odd}\left(L\right)) \implies ((\operatorname{Odd}\left(q\right)) \implies ((q \mid u \cdot L) \implies (\operatorname{residue}\left(q, u\right)^{j} \cdot \operatorname{residue}\left(q, \operatorname{A}\left(b, j\right)\right) = \sum_{h \in \operatorname{range}\left(L\right)} (\operatorname{residue}\left(q, (-1)\right)^{h} \cdot \operatorname{residue}\left(q, u \cdot \left(2 \cdot h + b\right)\right)^{j})))))))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerUpDownSource.scaled_moment` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive-order exponential derivatives contain the modulus. The remaining factor two is cancelled using oddness of q. This includes j=0.

E is ordinary A000111, defined in the naturals by the source recurrence A second derivative equals A times A first derivative. It differs from the weighted Entringer diagonal. U denotes ordinarySeries, a rational formal power series; derivatives and constants below are formal. The exact signed bridges are proved using complex rescaling and Riccati uniqueness, with no assumed EGF or congruence bridge.

**Definition 1.7 (The offset-zero ordinary recurrence).**

$$(\operatorname{E}\left(0\right) = 1) \land ((\operatorname{E}\left(1\right) = 1) \land (\forall n: \mathbb{N}, (\operatorname{E}\left(n + 2\right) = \sum_{i \in \operatorname{range}\left(n + 1\right)} (\operatorname{choose}\left(n, i\right) \cdot \operatorname{E}\left(i\right) \cdot \operatorname{E}\left(n + 1 - i\right)))))$$

*Formalization.* `D5/S1/Recurrence/Periodic/EulerUpDownSource.E` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

All subtraction in indices is natural subtraction; each term uses strictly earlier values.

**Definition 1.8 (The ordinary exponential series).**

$$U = \sum_{n \in \mathbb{N}} (\frac{\operatorname{E}\left(n\right) \cdot X^{n}}{\operatorname{factorial}\left(n\right)})$$

*Formalization.* `D5/S1/Recurrence/Periodic/EulerUpDownSource.ordinarySeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

U encodes the natural E coefficients in the rationals. X is the distinguished formal indeterminate.

**Theorem 1.9 (The source differential equation).**

$$(\operatorname{constantCoeff}\left(U\right) = 1) \land ((\operatorname{constantCoeff}\left(\operatorname{derivative}\left(U\right)\right) = 1) \land (\operatorname{derivative}\left(\operatorname{derivative}\left(U\right)\right) = U \cdot \operatorname{derivative}\left(U\right)))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerUpDownSource.source_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Coefficient multiplication recovers the defining positive recurrence exactly.

**Theorem 1.10 (The ordinary carrier is nondecreasing).**

$$\forall k: \mathbb{N}, (\forall l: \mathbb{N}, ((k \le l) \implies (\operatorname{E}\left(k\right) \le \operatorname{E}\left(l\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerUpDownSource.monotone_E` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zeroth summand of the positive source recurrence bounds the preceding value.

**Theorem 1.11 (The secant-plus-tangent equation).**

$$2 \cdot \operatorname{derivative}\left(U\right) = U^{2} + 1$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerUpDownSource.ordinary_riccati` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative of twice U prime minus U squared vanishes. Its constant coefficient is one.

**Theorem 1.12 (Exact even signed correspondence).**

$$\forall s: \mathbb{N}, (\operatorname{E}\left(2 \cdot s\right) = (-1)^{s} \cdot \operatorname{A}\left(1, 2 \cdot s\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerUpDownSource.signed_even` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality is in the integers. The source value at zero is included.

**Theorem 1.13 (Exact odd signed correspondence).**

$$\forall s: \mathbb{N}, (\operatorname{E}\left(2 \cdot s + 1\right) = (-1)^{s + 1} \cdot \operatorname{A}\left(0, 2 \cdot s + 1\right))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Periodic/EulerUpDownSource.signed_odd` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality is in the integers. The sign retains the ordinary positive tangent coefficients.

## References

- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.A`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.E`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.F`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.branch_equations`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.finite_identity`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.generating_identity`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.monotone_E`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.ordinarySeries`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.ordinary_riccati`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.scaled_moment`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.signed_even`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.signed_odd`
- Truth anchor: `D5/S1/Recurrence/Periodic/EulerUpDownSource.source_equation`
- Dependency: [D5/S1/Recurrence/Residue/QuarticEGFFixedPoint](../Residue/QuarticEGFFixedPoint.md)
