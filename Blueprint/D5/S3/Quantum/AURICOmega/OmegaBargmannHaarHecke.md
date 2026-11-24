# Rational quaternion geometry and harmonics

## Abstract

Exact projective quaternion geometry, even moments on the three-sphere, and quaternion divisibility.

**Theorem 1.1 (The normalized Gram determinant is nonnegative).**

$$\forall a \in \mathbb{Z}^{4}, b \in \mathbb{Z}^{4}, c \in \mathbb{Z}^{4},\; \left(\left(a \ne 0 \land b \ne 0\right) \land c \ne 0\right) \Rightarrow 0 \le \operatorname{detGram}\left(a, b, c\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.detGram3_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Clearing the positive product of squared norms gives the sum of the squares of the four maximal minors of the three coordinate rows.

**Theorem 1.2 (The doubled ray has zero Gram determinant).**

$$\forall a \in \mathbb{Z}^{4}, b \in \mathbb{Z}^{4},\; \left(a \ne 0 \land b \ne 0\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{detGram}\left(a, b, \operatorname{triad}\left(b, a, b\right)\right), 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.geodesic_doubling_detGram3_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The triad is twice the dot product times the second input minus its squared norm times the first input. Its squared norm is the first squared norm times the square of the second squared norm.

**Theorem 1.3 (Fidelity under great-circle doubling).**

$$\forall a \in \mathbb{Z}^{4}, b \in \mathbb{Z}^{4},\; \left(a \ne 0 \land b \ne 0\right) \Rightarrow \operatorname{Equivalent}\left(\operatorname{kappa}\left(a, \operatorname{triad}\left(b, a, b\right)\right), \left(2 \cdot \operatorname{kappa}\left(a, b\right) - 1\right)^{2}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.geodesic_doubling_kappa` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Squaring the dot product with the triad gives the numerator. The denominator is the square of the original product of squared norms.

**Theorem 1.4 (Consecutive even scalar-coordinate Haar moments).**

$$\forall k \in \mathbb{N},\; \operatorname{Equivalent}\left(\operatorname{moment}\left(k + 1\right), \operatorname{moment}\left(k\right) \cdot \frac{2 \cdot k + 1}{2 \cdot \left(k + 2\right)}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.haarKappaMoment_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The factorial functional is defined by the normalized three-sphere formula for even monomials. Cancelling the shared factorials and powers of four gives the recurrence for every natural degree.

**Theorem 1.5 (The first three even characters are orthonormal).**

$$\operatorname{Equivalent}\left(\operatorname{inner}\left(chi_{0}, chi_{0}\right), 1\right) \land \left(\operatorname{Equivalent}\left(\operatorname{inner}\left(chi_{0}, chi_{1}\right), 0\right) \land \left(\operatorname{Equivalent}\left(\operatorname{inner}\left(chi_{0}, chi_{2}\right), 0\right) \land \left(\operatorname{Equivalent}\left(\operatorname{inner}\left(chi_{1}, chi_{1}\right), 1\right) \land \left(\operatorname{Equivalent}\left(\operatorname{inner}\left(chi_{1}, chi_{2}\right), 0\right) \land \operatorname{Equivalent}\left(\operatorname{inner}\left(chi_{2}, chi_{2}\right), 1\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.peter_weyl_chi012_orthonormal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The characters have coefficient lists (1), (−1, 4), and (1, −12, 16). Convolving the coefficients and applying moments of degrees zero through four gives these six entries. The three reverse pairings also vanish by the exact coefficient products.

**Theorem 1.6 (The six-spinor Hecke sum has eigenvalue negative two fifths).**

$$\forall q \in \mathbb{Z}^{4},\; q \ne 0 \Rightarrow \operatorname{Equivalent}\left(\operatorname{hecke}\left(q\right), \frac{-2}{5} \cdot \operatorname{character}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.heckeT5_chi1_eigenvalue` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six right products each have five times the original squared norm. Pairing the opposite coordinate signs cancels the mixed terms in the squared scalar parts. The operator uses the unnormalized sum.

**Theorem 1.7 (The rational eigenvalue has positive Ramanujan margin).**

$$\operatorname{Equivalent}\left(4 \cdot 5 - (\frac{-2}{5})^{2}, \frac{496}{25}\right) \land 0 < \frac{496}{25}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.heckeT5_ramanujan_margin` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Subtracting the squared eigenvalue from four times five gives 496 over 25.

**Theorem 1.8 (Quaternion division by a nonzero integer is deterministic).**

$$\forall s \in \mathbb{Z}^{4}, A \in \mathbb{Z}^{4}, u \in \mathbb{Z}^{4}, v \in \mathbb{Z}^{4}, p \in \mathbb{Z},\; \left(p \ne 0 \land \left(\operatorname{mul}\left(s, A\right) = \operatorname{scale}\left(p, u\right) \land \operatorname{mul}\left(s, A\right) = \operatorname{scale}\left(p, v\right)\right)\right) \Rightarrow u = v$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.quaternion_fractran_deterministic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The transition equations give the same integer scaling of the two proposed outputs. Cancelling the nonzero factor in each coordinate identifies the outputs.

**Theorem 1.9 (The Y-unwind gate distinguishes equal-norm ordered products).**

$$\operatorname{normSq}\left(XY\right) = 25 \land \left(\operatorname{normSq}\left(YX\right) = 25 \land \left(\operatorname{mul}\left(XY, U\right) = \operatorname{scale}\left(5, X\right) \land \neg (\exists q \in \mathbb{Z}^{4},\; \operatorname{mul}\left(YX, U\right) = \operatorname{scale}\left(5, q\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.quaternion_fractran_order_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered states are (1, 2, 2, 4) and (1, 2, 2, −4). The unwind rotor is (1, 0, −2, 0) and the successful quotient is (1, 2, 0, 0). Right multiplication of YX by the unwind rotor gives second coordinate −6, which has no integral quotient by five.

## References

- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.detGram3_nonneg`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.geodesic_doubling_detGram3_zero`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.geodesic_doubling_kappa`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.haarKappaMoment_succ`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.heckeT5_chi1_eigenvalue`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.heckeT5_ramanujan_margin`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.peter_weyl_chi012_orthonormal`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.quaternion_fractran_deterministic`
- Truth anchor: `D5/S3/Quantum/AURICOmega/OmegaBargmannHaarHecke.quaternion_fractran_order_separation`
