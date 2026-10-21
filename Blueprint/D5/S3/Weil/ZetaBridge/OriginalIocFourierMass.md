# Original Ioc Fourier Mass

## Abstract

Original arbitrary complex Ioc L2 Fourier dictionary with literal dx mass.

The original interval is Ioc(-L/2,L/2), with literal zero extension. The phase-adjusted signed basis is (-1)^n exp(i*2*pi*n*x/L)/sqrt(L). All coefficients are complex and all signed integer modes are retained. No periodic endpoint equality, real or even restriction, or finite upper mode cutoff is imposed. Scientific statements and proof scope are given by the referenced Lean declarations.

**Definition 1.1 (Literal Ioc zero extension).**

$$\operatorname{iocZeroExtend}(L, f)=\operatorname{indicator}(\operatorname{Ioc}(-L2, L2), f)$$

*Formalization.* `D5/S3/Weil/ZetaBridge/OriginalIocFourierMass.iocZeroExtend` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The interval indicator retains the original Lebesgue dx measure and specifies the endpoint convention explicitly.

**Theorem 1.2 (Signed Parseval equals original dx mass).**

$$\operatorname{Positive}(L)\land \operatorname{MemLpIocTwo}(L, f)\Rightarrow \operatorname{tsum}(\operatorname{SignedCoeffSq}(L, f))=\operatorname{OriginalMass}(L, f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalIocFourierMass.tsum_signedCoeff_sq_eq_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The proof directly consumes tsum_sq_fourierCoeffOn and multiplies by L. The resulting coefficients are the actual signed phase-adjusted inner products, and the right side remains the original restricted Lebesgue mass.

**Theorem 1.3 (Centered exponential integral).**

$$\operatorname{Positive}(L)\Rightarrow \operatorname{IntegralCenteredExp}(L, s)=\operatorname{CenteredExpIntegral}(L, s)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalIocFourierMass.integral_centered_exp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-frequency branch is explicit. The nonzero branch uses the public interval exponential integral, so the rational form is only used away from resonance.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalIocFourierMass.integral_centered_exp`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalIocFourierMass.iocZeroExtend`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalIocFourierMass.tsum_signedCoeff_sq_eq_mass`
