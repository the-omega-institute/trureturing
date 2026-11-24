# Quadratic norms and rational Schur complements

## Abstract

Exact quadratic algebras and rational positivity for Chapter 32, section 32.8, and Appendix Q.

**Theorem 1.1 (Quadratic norms multiply).**

$$\forall b \in \mathbb{Z}, c \in \mathbb{Z},\; \forall z \in \operatorname{Quad}\left(b, c\right), w \in \operatorname{Quad}\left(b, c\right),\; \operatorname{N}\left(z \cdot w\right) = \operatorname{N}\left(z\right) \cdot \operatorname{N}\left(w\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.quadratic_norm_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The algebra uses the relation alpha squared equals b times alpha plus c. The norm is the scalar coefficient of the product with the conjugate.

**Theorem 1.2 (Inversion by nonzero norm).**

$$\forall b \in \mathbb{Z}, c \in \mathbb{Z},\; \forall z \in \operatorname{Quad}\left(b, c\right),\; \operatorname{N}\left(z\right) \ne 0 \Rightarrow z \cdot \operatorname{inv}\left(z\right) = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.quadratic_mul_inv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inverse divides the conjugate by the norm. Cross multiplication compares finite signed fractions, including negative norms.

**Theorem 1.3 (Fibonacci coefficients of golden powers).**

$$\forall n \in \mathbb{N},\; \varphi^{n + 1} = \operatorname{F}\left(n\right) + \operatorname{F}\left(n + 1\right) \cdot \varphi$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.phi_fibonacci` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying by the golden generator takes coefficients x and y to y and x plus y. The starting coefficients are zero and one.

**Theorem 1.4 (Norm of every golden power).**

$$\forall n \in \mathbb{N},\; \operatorname{N}\left(\varphi^{n}\right) = (-1)^{n}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.phi_power_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The generator has norm minus one, and the unit has norm one.

**Theorem 1.5 (The right-angle spinor closes after eight powers).**

$$\operatorname{normSq}\left(u\right) = 1 \land u^{8} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.sqrt_two_spinor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here u denotes the spinor with both coordinates equal to half the square-root-two generator. Its square has scalar coordinate zero and imaginary coordinate one.

**Theorem 1.6 (The squared CHSH value is eight).**

$$\left(2 \cdot \delta\right)^{2} = 8$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.sqrt_two_bell` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The square-root-two generator has square two.

**Theorem 1.7 (Lagrange's Gram identity).**

$$\forall s \in \operatorname{ListsOfPairs}\left(\mathbb{Q}\right),\; \operatorname{sumU}\left(s\right) \cdot \operatorname{sumV}\left(s\right) - \operatorname{sumUV}\left(s\right)^{2} = \operatorname{minorSquares}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.rational_lagrange_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The sequence s consists of pairs of rational coordinates. The sums sumU and sumV are the sums of coordinate squares, and sumUV is their dot product. The right side adds the squared alternating minors over all pairs of positions with the first position smaller than the second.

**Theorem 1.8 (Rational Cauchy–Schwarz).**

$$\forall s \in \operatorname{ListsOfPairs}\left(\mathbb{Q}\right),\; \operatorname{sumUV}\left(s\right)^{2} \le \operatorname{sumU}\left(s\right) \cdot \operatorname{sumV}\left(s\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.rational_cauchy_schwarz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each summand in the Gram identity is a rational square and therefore nonnegative.

**Theorem 1.9 (Schur completion of the square).**

$$\forall a \in \mathbb{Q}, b \in \mathbb{Q}, c \in \mathbb{Q}, x \in \mathbb{Q}, y \in \mathbb{Q},\; c \ne 0 \Rightarrow a \cdot x^{2} + 2 \cdot b \cdot x \cdot y + c \cdot y^{2} = \left(a - \frac{b^{2}}{c}\right) \cdot x^{2} + c \cdot \left(y + \frac{b}{c} \cdot x\right)^{2}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.rational_schur_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The pivot c is a finite nonzero rational. The correction to the first diagonal coefficient is b squared divided by c.

**Theorem 1.10 (The Schur residual is an attained minimum).**

$$\forall a \in \mathbb{Q}, b \in \mathbb{Q}, c \in \mathbb{Q}, x \in \mathbb{Q},\; 0 < c \Rightarrow \left(\left(\forall y \in \mathbb{Q},\; \left(a - \frac{b^{2}}{c}\right) \cdot x^{2} \le a \cdot x^{2} + 2 \cdot b \cdot x \cdot y + c \cdot y^{2}\right) \land a \cdot x^{2} + 2 \cdot b \cdot x \cdot \operatorname{neg}\left(\frac{b}{c} \cdot x\right) + c \cdot \operatorname{neg}\left(\frac{b}{c} \cdot x\right)^{2} = \left(a - \frac{b^{2}}{c}\right) \cdot x^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.rational_schur_min` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

With a positive pivot the completed square is nonnegative. It vanishes at y equal to the negative of the shift.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.phi_fibonacci`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.phi_power_norm`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.quadratic_mul_inv`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.quadratic_norm_mul`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.rational_cauchy_schwarz`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.rational_lagrange_gram`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.rational_schur_complete`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.rational_schur_min`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.sqrt_two_bell`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaQuadraticAndSchur.sqrt_two_spinor`
