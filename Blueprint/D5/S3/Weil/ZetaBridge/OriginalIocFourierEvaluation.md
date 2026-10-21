# Original Ioc Fourier Evaluation

## Abstract

Original arbitrary complex Ioc L2 Fourier dictionary with literal dx mass.

The original interval is Ioc(-L/2,L/2), with literal zero extension. The phase-adjusted signed basis is (-1)^n exp(i*2*pi*n*x/L)/sqrt(L). All coefficients are complex and all signed integer modes are retained. No periodic endpoint equality, real or even restriction, or finite upper mode cutoff is imposed. Scientific statements and proof scope are given by the referenced Lean declarations.

**Theorem 1.1 (Bounded evaluation of the complete complex L2 expansion).**

$$\operatorname{Positive}(L)\land \operatorname{MemLpIocTwo}(L, f)\Rightarrow \operatorname{HasSum}(\operatorname{SignedCoeffTimesBasisFT}(L, f), \operatorname{paperFT}(\operatorname{iocZeroExtend}(L, f)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalIocFourierEvaluation.hasSum_signedCoeff_mul_basisPaperFT` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Ioc MemLp representative and the negative-exponent evaluation kernel are lifted literally to AddCircle. The latter has norm one and is in L2. HilbertBasis.hasSum_inner_mul_inner for the public fourierBasis gives an integral pairing identity. The proof identifies both inner products and cancels normalized Haar and the two signed phases. It uses no pointwise Fourier inversion or periodic endpoint condition.

**Theorem 1.2 (Signed coefficients are the actual dx inner products).**

$$\operatorname{Positive}(L)\Rightarrow \operatorname{signedCoeff}(L, f, n)=\operatorname{OriginalBasisInnerProduct}(L, f, n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalIocFourierEvaluation.signedCoeff_eq_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The integral coefficient formula follows from the normalized Haar coefficient after restoring the square-root length and signed phase.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalIocFourierEvaluation.hasSum_signedCoeff_mul_basisPaperFT`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalIocFourierEvaluation.signedCoeff_eq_integral`
- Dependency: [D5/S3/Weil/ZetaBridge/OriginalIocFourierMass](OriginalIocFourierMass.md)
