# CycleGeodesicMidpoint

## Abstract

The midpoint formula holds with a uniform quadratic error and even-dimensional vanishing.

**Definition 1.1 (midpointScale).**

$$\forall n \in \mathbb{N},\; \operatorname{midpointScale}\left(n\right) = \left(-1\right)^{\operatorname{Nat.div}\left(\operatorname{Nat.sub}\left(n, 1\right), 2\right)} \cdot 2 \cdot (\operatorname{Real.exp}\left(-(n:\mathbb{R})\right):\mathbb{C})$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointScale` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

The alternating leading scale uses natural subtraction and natural division in its exponent, namely Nat.div (Nat.sub n 1) 2. The real exponential is cast to the complex numbers.

**Theorem 1.2 (midpoint_even_of_product).**

$$ProductFormula \Rightarrow \left(\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{Even}\left(n\right) \Rightarrow \operatorname{Matrix.permanent}\left(\operatorname{gamma}\left(n, \frac{1}{2}\right)\right) = 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpoint_even_of_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

For a positive even dimension, the middle factor in the product is zero.

**Definition 1.3 (stirlingError).**

$$\forall n \in \mathbb{N},\; \operatorname{stirlingError}\left(n\right) = \operatorname{Real.log}\left(\operatorname{Stirling.stirlingSeq}\left(n\right)\right) - \operatorname{Real.log}\left(\operatorname{Real.sqrt}\left(\operatorname{Real.pi}\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.stirlingError` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

This logarithmic error measures the Stirling sequence relative to its limiting value.

**Definition 1.4 (midpointAmplitude).**

$$\forall m \in \mathbb{N},\; \operatorname{midpointAmplitude}\left(m\right) = \frac{(\operatorname{Nat.factorial}\left(2 \cdot m + 1\right):\mathbb{R})^{2}}{2^{2 \cdot m} \cdot (\operatorname{Nat.factorial}\left(m\right):\mathbb{R})^{2} \cdot \left(2 \cdot (m:\mathbb{R}) + 1\right)^{2 \cdot m + 2}}$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointAmplitude` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

The positive amplitude is the literal factorial expression for an odd dimension.

**Definition 1.5 (midpointRatio).**

$$\forall m \in \mathbb{N},\; \operatorname{midpointRatio}\left(m\right) = \frac{\operatorname{midpointAmplitude}\left(m\right)}{2 \cdot \operatorname{Real.exp}\left(-\left(2 \cdot (m:\mathbb{R}) + 1\right)\right)}$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointRatio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

The amplitude is normalized by its leading exponential scale.

**Definition 1.6 (midpointLogRatio).**

$$\forall m \in \mathbb{N},\; \operatorname{midpointLogRatio}\left(m\right) = \left(2 \cdot (m:\mathbb{R}) + 1\right) \cdot \left(-\operatorname{Real.log}\left(1 - \frac{1}{2 \cdot (m:\mathbb{R}) + 1}\right)\right) - 1 + 2 \cdot \operatorname{stirlingError}\left(2 \cdot m + 1\right) - 2 \cdot \operatorname{stirlingError}\left(m\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointLogRatio` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

The expression separates the logarithmic mesh correction from the two Stirling errors.

**Theorem 1.7 (midpointAmplitude_pos).**

$$\forall m \in \mathbb{N},\; 0 < \operatorname{midpointAmplitude}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointAmplitude_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

Every factorial and denominator factor is positive.

**Theorem 1.8 (product_odd_amplitude).**

$$\forall m \in \mathbb{N},\; \operatorname{productValue}\left(2 \cdot m + 1, -1\right) = \left(-1\right)^{m} \cdot (\operatorname{midpointAmplitude}\left(m\right):\mathbb{C})$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.product_odd_amplitude` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

Splitting the odd factors into positive and negative factors gives the alternating amplitude.

**Theorem 1.9 (midpoint_ratio_of_product).**

$$ProductFormula \Rightarrow \left(\forall m \in \mathbb{N},\; \frac{\operatorname{Matrix.permanent}\left(\operatorname{gamma}\left(2 \cdot m + 1, \frac{1}{2}\right)\right)}{\operatorname{midpointScale}\left(2 \cdot m + 1\right)} = (\operatorname{midpointRatio}\left(m\right):\mathbb{C})\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpoint_ratio_of_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

The exact product identifies the permanent ratio with the positive real ratio.

**Theorem 1.10 (log_midpointRatio).**

$$\forall m \in \mathbb{N},\; m \ne 0 \Rightarrow \operatorname{Real.log}\left(\operatorname{midpointRatio}\left(m\right)\right) = \operatorname{midpointLogRatio}\left(m\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.log_midpointRatio` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

The logarithmic factorial identity applies for positive m.

**Theorem 1.11 (midpointLogRatio_abs_le).**

$$\forall m \in \mathbb{N},\; 1 \le m \Rightarrow \left|\operatorname{midpointLogRatio}\left(m\right)\right| \le \frac{2}{2 \cdot (m:\mathbb{R}) + 1}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointLogRatio_abs_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

Telescoping the Stirling bounds gives a logarithmic error bounded by twice the reciprocal dimension.

**Theorem 1.12 (midpointRatio_second_order).**

$$\forall m \in \mathbb{N},\; \left|\operatorname{midpointRatio}\left(m\right) - 1 - \frac{1}{3 \cdot \left(2 \cdot (m:\mathbb{R}) + 1\right)}\right| \le \frac{16}{\left(2 \cdot (m:\mathbb{R}) + 1\right)^{2}}$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointRatio_second_order` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

The explicit remainder is uniform over every odd positive dimension, including n = 1.

**Definition 1.13 (claim2).**

$$claim2 \Leftrightarrow \left((\exists C \in \mathbb{R},\; (0 \le C) \land (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{Odd}\left(n\right) \Rightarrow \left\lVert \frac{\operatorname{Matrix.permanent}\left(\operatorname{gamma}\left(n, \frac{1}{2}\right)\right)}{\operatorname{midpointScale}\left(n\right)} - 1 - \frac{1}{3 \cdot (n:\mathbb{C})} \right\rVert \le \frac{C}{(n:\mathbb{R})^{2}}\right))) \land (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{Even}\left(n\right) \Rightarrow \operatorname{Matrix.permanent}\left(\operatorname{gamma}\left(n, \frac{1}{2}\right)\right) = 0\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.claim2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

Page 19, Section 8.4, Open Problem 2: "Prove the midpoint formula perm(γ(1/2)) = (-1)^((n-1)/2) · 2e^(-n)(1 + 1/(3n) + O(n^(-2)))." The norm bound encodes the big-O term uniformly over positive odd n. Observation 5 on page 8 supplies the even-dimensional zero clause.

**Theorem 1.14 (result2).**

$$(\exists C \in \mathbb{R},\; (0 \le C) \land (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{Odd}\left(n\right) \Rightarrow \left\lVert \frac{\operatorname{Matrix.permanent}\left(\operatorname{gamma}\left(n, \frac{1}{2}\right)\right)}{\operatorname{midpointScale}\left(n\right)} - 1 - \frac{1}{3 \cdot (n:\mathbb{C})} \right\rVert \le \frac{C}{(n:\mathbb{R})^{2}}\right))) \land (\forall n \in \mathbb{N},\; 1 \le n \Rightarrow \left(\operatorname{Even}\left(n\right) \Rightarrow \operatorname{Matrix.permanent}\left(\operatorname{gamma}\left(n, \frac{1}{2}\right)\right) = 0\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.result2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Igor Rivin (2026). *Permanents of matrix ensembles: computation, distribution, and geometry*. URL: <https://arxiv.org/abs/2602.10141v3>.

*Commentary.*

The permanent has the stated alternating exponential scale and the 1/(3n) correction. A single constant C = 16 works for all positive odd n; every positive even n gives zero.

## References

- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.claim2`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.log_midpointRatio`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointAmplitude`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointAmplitude_pos`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointLogRatio`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointLogRatio_abs_le`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointRatio`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointRatio_second_order`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpointScale`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpoint_even_of_product`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.midpoint_ratio_of_product`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.product_odd_amplitude`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.result2`
- Truth anchor: `D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicMidpoint.stirlingError`
- Dependency: [D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicProduct](CycleGeodesicProduct.md)
