# Golden Contraction Radical Bound

## Abstract

The contraction-face logarithmic error is controlled by the prime radical.

**Theorem 1.1 (The hidden-product error lies in a golden radical window).**

$$\forall n\in\mathbb{N},\ -\varphi^{-2} \cdot \log{\operatorname{rad}(n)} \leq \log{nS n} - \varphi \cdot \log{n} \leq \varphi^{-1} \cdot \log{\operatorname{rad}(n)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenContractionRadicalBound.log_nS_error_radical_window` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The shifted Zeckendorf Beatty formula places each substituted exponent minus phi times the original exponent between minus phi to the negative second power and phi inverse. Prime logarithms are nonnegative, so summing those pointwise inequalities over the factorization gives the displayed window. The sum of the prime logarithms is exactly the logarithm of the product of the distinct prime factors.

**Theorem 1.2 (The contraction-face length has the documented radical bound).**

$$\forall n\in\mathbb{N},\ n\neq0 \implies \lvert\lambda_{-}(n)\rvert \leq \varphi^{-1} \cdot \log{\operatorname{rad}(n)}$$

*Proof.* Machine-checked in Lean as `D5/S1/Deficit/Displacement/GoldenContractionRadicalBound.abs_lambdaMinus_le_goldenRatio_inv_log_primeRadical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frozen contraction-face closed form identifies lambda minus with the middle error term in the first theorem. Since zero is less than phi inverse and phi inverse is at most one, the sharper lower constant phi to the negative second power is no larger than phi inverse. The two sides therefore combine through the absolute-value criterion to give the stated bound.

## References

- Truth anchor: `D5/S1/Deficit/Displacement/GoldenContractionRadicalBound.abs_lambdaMinus_le_goldenRatio_inv_log_primeRadical`
- Truth anchor: `D5/S1/Deficit/Displacement/GoldenContractionRadicalBound.log_nS_error_radical_window`
- Dependency: [D5/S1/Deficit/Displacement/GoldenDesubstitutionClosedForms](GoldenDesubstitutionClosedForms.md)
