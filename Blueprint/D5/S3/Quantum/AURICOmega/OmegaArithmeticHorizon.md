# The computable arithmetic horizon

## Abstract

Zero-axiom arithmetic for Chapter 32, sections 32.7 and 32.8, and Appendix Q.

**Theorem 1.1 (Prime escape from a finite list).**

$$\forall S \in NatList,\; 0 < \operatorname{prod}\left(S\right) \Rightarrow \left(\exists p \in \mathbb{N},\; \operatorname{IsPrime}\left(p\right) \land \left(p \mid \operatorname{prod}\left(S\right) + 1 \land \left(\neg p \in S\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.euclid_prime_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every list member greater than one leaves remainder one on dividing the successor of the product. A positive product makes that successor at least two, so a prime divisor exists and is outside the list. The empty list has product one.

**Theorem 1.2 (Signed Bézout coefficients).**

$$\forall a \in \mathbb{N}, b \in \mathbb{N},\; \exists x \in \mathbb{Z}, y \in \mathbb{Z},\; a \cdot x + b \cdot y = \operatorname{gcd}\left(a, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.bezout_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Euclidean algorithm updates the coefficients when replacing the inputs by the divisor and remainder. The identity includes both zero inputs.

**Theorem 1.3 (Alternating determinant of successive continuants).**

$$\forall S \in NatList,\; \operatorname{determinant}\left(S\right) = {-1}^{\operatorname{length}\left(S\right)}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.cf_convergent_determinant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The determinant is the current numerator times the preceding denominator minus the preceding numerator times the current denominator. Appending a coefficient reverses its sign. Adjacent convergents at indices n and n+1 use n+2 coefficients, so this is the Euler–Wallis sign at index n.

**Theorem 1.4 (Every convergent has coprime coordinates).**

$$\forall S \in NatList,\; \forall d \in \mathbb{N},\; \left(d \mid \operatorname{numerator}\left(S\right) \land d \mid \operatorname{denominator}\left(S\right)\right) \Rightarrow d = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.cf_convergent_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The coordinates refer to the current continuant of the list. A common divisor divides the magnitude of its unit determinant with the preceding continuant, including at the first convergent.

**Theorem 1.5 (Machin's exact rational tangent chain).**

$$machinChain \equiv 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.machin_rational_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Double 1/5 using tangent addition to obtain 5/12, then double again to obtain 120/119. Subtract 1/239 using tangent subtraction. Using the reduced 120/119 intermediate, the final homogeneous product has numerator and denominator 28561 before reduction.

**Theorem 1.6 (Integer quarter-depth soundness).**

$$\forall c \in \mathbb{N}, d \in \mathbb{N}, p \in \mathbb{N}, q \in \mathbb{N}, N \in \mathbb{N},\; \left(0 < d \land \left(0 < p \land \operatorname{quarterDepth}\left(c, d, p, q\right) \le N\right)\right) \Rightarrow c \cdot q < d \cdot p \cdot 4^{N + 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.quarterDepth_integer_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The search finds the least depth whose next power of four, multiplied by dp, strictly exceeds cq. When q is positive the library also gives the strict comparison of the corresponding exact ratios.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.bezout_identity`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.cf_convergent_coprime`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.cf_convergent_determinant`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.euclid_prime_escape`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.machin_rational_chain`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaArithmeticHorizon.quarterDepth_integer_sound`
