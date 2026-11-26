# Monomial and analytic substitution

## Abstract

Inverse half-current Taylor coefficients

**Theorem 1.1 (Inverse transport of a monomial).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMInverseJets.coefficient_rawLocal_pow_div_halfJacobian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMInverseJets.coefficient_rawLocal_pow_div_halfJacobian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For real 0 < x < 1, any chart and any puncture, take the physical Taylor coefficient of degree m of the inverse coordinate to the native power n divided by the half-Jacobian evaluated on the chosen inverse branch. It vanishes for n > m. For n ≤ m it is the inverse lifted scale times the inverse scale to power m, times the negative lowering parameter to power m−n and the generalized binomial coefficient with top m+1/2 and bottom m−n.

**Theorem 1.2 (Finite substitution for an analytic germ).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMInverseJets.coefficient_comp_rawLocal_div_halfJacobian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMInverseJets.coefficient_comp_rawLocal_div_halfJacobian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same chart hypotheses, for any complex germ analytic at zero, the physical Taylor coefficient of degree m after inverse substitution and division by the half-Jacobian is a finite sum over native degrees 0 through m. Each summand is the native Taylor coefficient times its inverse monomial factor. The Taylor remainder after degree m is divisible by the physical coordinate to power m+1.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMInverseJets.coefficient_comp_rawLocal_div_halfJacobian`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMInverseJets.coefficient_rawLocal_pow_div_halfJacobian`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/FourPointChannelCoefficients](FourPointChannelCoefficients.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccupationTransport](OriginalFourMOccupationTransport.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitTaylor](OriginalFourMSlitTaylor.md)
