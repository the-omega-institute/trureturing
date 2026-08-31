# First Li Coefficient Normalization

## Abstract

The first Li coefficient normalizes the completed-zeta logarithmic derivative at one.

**Theorem 1.1 (The first Li coefficient gives unit normalization).**

$$\operatorname{let} lambda_{1}: \mathbb{R}:=1 + \frac{\operatorname{eulerMascheroniConstant}\left(\right)}{2} - \operatorname{log}\left(2 \cdot \operatorname{sqrt}\left(\pi\right)\right); \frac{\operatorname{deriv}\left(xiReading, 1\right)}{\operatorname{xiReading}\left(1\right)} = \operatorname{complex}\left(lambda_{1}\right) \land \frac{1}{\operatorname{complex}\left(lambda_{1}\right)} \cdot \frac{\operatorname{deriv}\left(xiReading, 1\right)}{\operatorname{xiReading}\left(1\right)} = 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/Endpoints/FirstLiCoefficientNormalization.first_li_coefficient_normalization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public first coefficient is the source's explicit real constant one plus one half of the Euler-Mascheroni constant minus the logarithm of twice the square root of pi. The first conjunct identifies it with the logarithmic derivative of the canonical xi reading at one.

The proof differentiates the frozen pole-removed xi formula and reuses the frozen endpoint value xiReading(1) = 1/2. Certified rational bounds for the Euler-Mascheroni constant, pi, and the exponential series prove that the coefficient is positive, so reciprocal cancellation yields the second public conjunct.

## References

- Truth anchor: `D5/S3/Zeros/Endpoints/FirstLiCoefficientNormalization.first_li_coefficient_normalization`
- Dependency: [D5/S3/Zeros/Endpoints/XiEndpointValues](XiEndpointValues.md)
