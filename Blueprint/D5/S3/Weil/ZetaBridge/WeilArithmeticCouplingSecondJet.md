# Weil Arithmetic Coupling Second Jet

## Abstract

The concrete prime-pole-Gamma divided-difference column has a second exterior jet whose remainder gains an additional N/|m| factor.

The source imports the already bounded arithmetic boundary symbol from WeilArithmeticCouplingJet. It keeps the zeroth and first powers of the interior Fourier index in the exact expansion of 1/(m-n). No replacement of the prime or Gamma terms by an asymptotic model is made.

**Theorem 1.1 (Second exterior jet for the actual arithmetic coupling).**

$$\operatorname{interiorBand}(N)\land \operatorname{outside}(m, N)\Rightarrow \operatorname{norm}(\operatorname{column}(c, v, m)-\operatorname{secondJet}(c, v, m))\leq \frac{2 \operatorname{BArith}(c) N^{{2}}}{\pi \operatorname{abs}(m)^{{2}} {\operatorname{abs}(m)-N}} \operatorname{l1}(v)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingSecondJet.arithmetic_coupling_second_jet_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact scalar identity is 1/(m-n)=1/m+n/m^2+n^2/(m^2(m-n)). The previously proved uniform arithmetic boundary budget bounds the last numerator. For |n|<=N<|m| this gives a pointwise remainder proportional to N^2/(|m|^2(|m|-N)). After square summation over |m|>M, the remainder therefore improves by order (N/M)^2 relative to the first jet. The infinite low-rank Gram assembly is deliberately left to the arithmetic certificate rather than asserted as part of this pointwise theorem.

## References

- Truth anchor: `D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingSecondJet.arithmetic_coupling_second_jet_error`
- Dependency: [D5/S3/Weil/ZetaBridge/WeilArithmeticCouplingJet](WeilArithmeticCouplingJet.md)
