# Weil Arithmetic Coupling Parity Gram

## Abstract

The concrete arithmetic symbol is odd; reflection pairing retains four boundary moments in two positive moment Gram blocks.

s(c,n) is exactly arithmeticBoundarySymbol from WeilArithmeticCouplingJet, including the pole, infinite Gamma series and finite von Mangoldt sine sum. J2 is exactly couplingSecondJet from WeilArithmeticCouplingSecondJet. Neither the Weil form nor its Fourier normalization is redefined.

**Theorem 1.1 (Reflection of the actual arithmetic symbol).**

$$\operatorname{s}(c, -n)=-\operatorname{s}(c, n)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram.arithmetic_boundary_symbol_neg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The identity holds for every natural c and integer n. The arithmetic application uses c>=2, where the imported source independently proves absolute convergence. Each pole and Gamma numerator is odd in the Fourier frequency and its denominator is even; the finite prime sum is odd by the sine identity. Oddness is proved rather than assumed.

**Theorem 1.2 (Exact paired second-jet energy).**

$$\operatorname{Nonzero}(m)\Rightarrow \operatorname{normSq}(\operatorname{J2}(c, S, v, m))+\operatorname{normSq}(\operatorname{J2}(c, S, v, -m))=\operatorname{div}(2, \operatorname{square}(pi) \operatorname{square}(m)) {\operatorname{normSq}(\operatorname{U}(m))+\operatorname{normSq}(\operatorname{V}(m))}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram.arithmetic_second_jet_pair_energy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

S is any finite integer set and v is any complex coefficient family. A0=sum v_n, B0=sum s_n*v_n, A1=sum n*v_n, B1=sum n*s_n*v_n. U_m=-s_m*A0+B1/m and V_m=B0-s_m*A1/m. The collected jets are J2(m)=(U_m+V_m)/(pi*m) and J2(-m)=(U_m-V_m)/(pi*m). The complex parallelogram identity proves the displayed result. No coefficient parity, reality or boundary-moment cancellation is assumed. Summing over positive exterior indices gives two positive 2-by-2 moment Gram blocks. The infinite summation, its scalar remainder, the executable c=3 enclosure certificate and the Fourier/domain identification are separate paper/computer-assisted steps in the existing RH source analysis. This declaration does not prove an unbounded-scale Xi limit.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram.arithmetic_boundary_symbol_neg`
- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingParityGram.arithmetic_second_jet_pair_energy`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingSecondJet](WeilArithmeticCouplingSecondJet.md)
