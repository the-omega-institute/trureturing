# Original Half-Fock Oscillator Coefficient Adjoints

## Abstract

Original Half-Fock Oscillator Coefficient Adjoints

This proof acts on the literal oscillatorCoefficient in LatticeHalfFockChargedTensorCoefficients. Its summands remain oscillatorTerm(D,a,M,P,d) = coeff(d,halfTranslatedPolynomial(D,a,P)) times halfCreationCoeff(D,a,M+chargeNorm(D,a)+d). The sum is supported in the actual finite support of the translated polynomial. The original sum, creation commutation and current Ward suppliers are used directly, including their private original declarations; no alternative convolution operator or fixed coefficient cutoff is introduced.

**Theorem 1.1 (All Charges, Exponents and Oscillator Pairs).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockConvolutionAdjoint.oscillator_coefficient_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockConvolutionAdjoint.oscillator_coefficient_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact reflected charge is -a and the exact reflected exponent is -M-2*chargeNorm(D,a). To derive the index, write A=M+chargeNorm(D,a). The constant coefficient of the original oscillator sum only retains translated degree -A when A is nonpositive. Charge reflection leaves the norm unchanged; hence the reflected total creation index must equal -A, which forces the displayed exponent. The full proof extends the already established creation/translation transpose by structural induction on the complete finite input polynomial P, generalizing the exponent and the entire target Q. In the creation step, the original coefficient creator law shifts M by 2k+1; the actual positive-current Ward law on the reflected target shifts the reflected exponent by -(2k+1). Their equality is proved in integer arithmetic. This maintains normal order without interchanging unrestricted infinite series or imposing an arbitrary cutoff.

Proof shape: content. The new earning inference is the full original coefficient transpose for arbitrary states and exponents; the original Ward, support and constant-vacuum suppliers are consumed and receive no new mathematical credit. No positivity, unitarity, primary-state, Gram-inverse or scalar-evaluation premise is used. In particular the algebraic theorem includes rank zero and indefinite original Gram matrices. Both inverse-Gram equations remain required only by the separate nondegeneracy statements that this proof does not need. LatticeConvolutionFockAdjoint supplies the prior integer-frequency proof architecture. Classical twisted lattice Fock geometry is the provenance, with no literature novelty claim. The owning Reg source binds the exact original operator telescope and actual four-family obligations.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockConvolutionAdjoint.oscillator_coefficient_adjoint`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockCreationTranslationAdjoint](LatticeHalfFockCreationTranslationAdjoint.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockChargedTensorCoefficients](../../LatticeHalfFockChargedTensorCoefficients.md)
