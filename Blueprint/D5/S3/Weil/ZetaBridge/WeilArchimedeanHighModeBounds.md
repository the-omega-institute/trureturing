# Weil Archimedean High-Mode Bounds

## Abstract

The actual Gamma symbol and diagonal correction have frequency-decaying bounds, supplying the constants for energy-weighted Weil elimination.

Use the existing arithmeticBoundarySymbol s(c,n), with c a natural number at least 2, L=log(c), omega=2*pi*n/L and integer n nonzero. Write beta_j=2*j+1/2 and R_j=(1-exp(-beta_j*L)) *(beta_j^2-omega^2)/(beta_j^2+omega^2)^2. GammaPart means s(c,n) plus its explicit pole and finite prime terms, so it is exactly the negative Gamma series already in the canonical arithmetic symbol. There is no second Weil definition.

**Theorem 1.1 (Frequency-sensitive arithmetic Gamma bounds).**

$$\operatorname{And}(\operatorname{AtLeast}(c, 2), \operatorname{Nonzero}(n))\Rightarrow \operatorname{And}(\operatorname{LessEqual}(\operatorname{abs}(\operatorname{GammaPart}(c, n)), 1+\operatorname{div}(L, \operatorname{mul}(2, pi, \operatorname{abs}(n)))), \operatorname{SummableNorm}(R), \operatorname{LessEqual}(\operatorname{abs}(\operatorname{mul}(\operatorname{div}(2, L), \operatorname{tsum}(R))), \operatorname{div}(1, \operatorname{mul}(pi, \operatorname{abs}(n)))+\operatorname{div}(L, \operatorname{mul}(2, \operatorname{square}(pi), \operatorname{square}(n)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArchimedeanHighModeBounds.arithmetic_archimedean_high_mode_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A positive telescoping estimate for j>=1 bounds the majorant sum omega/(beta_j^2+omega^2) by omega/(omega+1/2). The zeroth term is at most 1/omega. Hence the complete majorant is at most 1+1/omega. Its bounded nonnegative partial sums also prove convergence. The actual sine series is dominated termwise because 0<=1-exp(-beta_j*L)<=1.

For the correction use |beta_j^2-omega^2|<=beta_j^2+omega^2. Its absolute series is dominated by the same summable majorant divided by |omega|. Multiplication by 2/L and |omega|=2*pi*|n|/L gives the displayed diagonal error. Absolute summability is proved, so totalized divergent series cannot make either bound vacuous.

The same-source Fourier calculation identifies this series as the actual Gamma diagonal correction. Combining the new symbol bound with the classical integer discrete-Hilbert norm at most pi controls every off-diagonal mode. The resulting simultaneous logarithmic form lower bound, weighted Schur completion and executed c=3 interval certificate are proved separately in the existing RH source analysis. They are not conclusions of this Lean declaration. Lean and Scribe compilation were not run in this research session.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArchimedeanHighModeBounds.arithmetic_archimedean_high_mode_bounds`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet](WeilArithmeticCouplingJet.md)
