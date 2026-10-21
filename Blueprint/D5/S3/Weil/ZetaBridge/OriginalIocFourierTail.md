# Original Ioc Fourier Tail

## Abstract

Original arbitrary complex Ioc L2 Fourier dictionary with literal dx mass.

The original interval is Ioc(-L/2,L/2), with literal zero extension. The phase-adjusted signed basis is (-1)^n exp(i*2*pi*n*x/L)/sqrt(L). All coefficients are complex and all signed integer modes are retained. No periodic endpoint equality, real or even restriction, or finite upper mode cutoff is imposed. Scientific statements and proof scope are given by the referenced Lean declarations.

**Theorem 1.1 (Two actual ordered tails exhaust the original mass).**

$$\operatorname{Positive}(L)\land \operatorname{MemLpIocTwo}(L, f)\land \operatorname{LowSignedCoefficientsZero}(L, N, f)\Rightarrow \operatorname{BothTailsSquareSummable}(L, N, f)\land \operatorname{ActualTailMassSum}(L, N, f)=\operatorname{OriginalMass}(L, f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalIocFourierTail.signedCoeff_tail_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

positiveTail and negativeTail select N+j+1 and -(N+j+1). The proof splits a summable integer series into nonnegative and negative-successor parts, pays their different shifts N+1 and N, and kills only genuine low coefficients. Parseval leaves the right side as the original dx integral of the squared norm.

**Theorem 1.2 (Literal PLUS transform is the signed exterior series).**

$$\operatorname{Positive}(L)\land \operatorname{Positive}(N)\land \operatorname{MemLpIocTwo}(L, f)\land \operatorname{QuarterBand}(N, s)\land \operatorname{LowSignedCoefficientsZero}(L, N, f)\Rightarrow \operatorname{paperFT}(\operatorname{iocZeroExtend}(L, f), \operatorname{PhysicalFrequency}(L, s))=\operatorname{SqrtLOverPiSin}(L, s) \operatorname{exteriorSeries}(N, \operatorname{signedCoeff}(L, f), s)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalIocFourierTail.paperFT_eq_exteriorSeries` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The resonance-safe sinc basis transform is proved first. In the quarter band, each remaining signed mode is separated from every pole. Integer sine translation cancels the basis phase. The positive tail has denominator N+s+j+1; the negative tail contributes the minus sign and denominator N-s+j+1. These are the actual complex coefficients, with no parity assumption.

**Theorem 1.3 (Original squared transform equals the public exterior density).**

$$\operatorname{Positive}(L)\land \operatorname{Positive}(N)\land \operatorname{MemLpIocTwo}(L, f)\land \operatorname{QuarterBand}(N, s)\land \operatorname{LowSignedCoefficientsZero}(L, N, f)\Rightarrow {\operatorname{NormActualPaperFT}(L, f, s)}^{2}=\operatorname{exteriorFourierDensity}(L, N, \operatorname{positiveTail}(N, \operatorname{signedCoeff}(L, f)), \operatorname{negativeTail}(N, \operatorname{signedCoeff}(L, f)), s)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalIocFourierTail.norm_paperFT_sq_eq_exteriorFourierDensity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Taking the squared complex norm of the exact signed transform identity gives the public density with the actual positive and negative tails.

**Theorem 1.4 (Physical leakage on the exact public quarter band).**

$$\operatorname{Positive}(N)\land \operatorname{Positive}(L)\land \operatorname{MemLpIocTwo}(L, f)\land \operatorname{LowSignedCoefficientsZero}(L, N, f)\Rightarrow \operatorname{PhysicalBandIntegrable}(L, N, f)\land \operatorname{NormalizedPhysicalIntegral}(L, N, f)\leq \operatorname{div}(4, 3 {pi}^{2}) \operatorname{OriginalMass}(L, f)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/OriginalIocFourierTail.original_low_frequency_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The body consumes only the public WeilInfiniteComplementLeakage.infinite_complement_low_frequency_mass. Its band is abs(s) <= N/4. Substitution t=2*pi*s/L yields abs(t) <= pi*N/(2*L) and dt/(2*pi)=ds/L, with interval integrability transported explicitly. The constant is 4/(3*pi^2). No private Cauchy theorem, separate half band estimate, full Weil positivity, Schur conclusion, Robin statement or RH conclusion is used.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalIocFourierTail.norm_paperFT_sq_eq_exteriorFourierDensity`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalIocFourierTail.original_low_frequency_mass`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalIocFourierTail.paperFT_eq_exteriorSeries`
- Truth anchor: `D5/S3/Weil/ZetaBridge/OriginalIocFourierTail.signedCoeff_tail_mass`
- Dependency: [D5/S3/Weil/ZetaBridge/OriginalIocFourierEvaluation](OriginalIocFourierEvaluation.md)
- Dependency: [D5/S3/Weil/ZetaBridge/WeilInfiniteComplementLeakage](WeilInfiniteComplementLeakage.md)
