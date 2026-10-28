# Cubic radial trace compatibility

## Abstract

Sharp cubic compatibility for arbitrary finite Hermitian matrix pencils with a radial denominator.

**Definition 1.1 (The rational trace function).**

Lean statement: `D5/S3/Quantum/Matrix/HsfCubicRadial.cubicRadialTrace`

*Formalization.* `D5/S3/Quantum/Matrix/HsfCubicRadial.cubicRadialTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For complex matrices A and B and real k, define f(t)=Re Tr((A+tB)^3)/(1+kt)^2. This is the actual scalar function, with its usual real derivatives. Its denominator is nonzero on a neighborhood of zero.

**Theorem 1.2 (Second and third derivatives).**

Lean statement: `D5/S3/Quantum/Matrix/HsfCubicRadial.cubic_derivatives`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfCubicRadial.cubic_derivatives` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type, arbitrary complex square matrices A and B, and real k, put E=B-kA. Then f''(0)=6 Re Tr(A E^2) and f'''(0)=6 Re Tr((B-4kA) E^2). No Hermitian or positivity hypotheses are needed for these identities. Expanding the cubic and using cyclicity of trace gives a scalar cubic numerator. Repeated quotient differentiation near zero proves the identities for iteratedDeriv, including differentiability on the neighborhood where the denominator is nonzero.

**Theorem 1.3 (The noncommutative cubic estimate).**

Lean statement: `D5/S3/Quantum/Matrix/HsfCubicRadial.cubic_radial_compatibility`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfCubicRadial.cubic_radial_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite index type, Hermitian A and B with A+B and A-B positive semidefinite, and every real k, one has f''(0)>=0 and |f'''(0)|<=(1+4|k|)f''(0). Thus |k|<=1 gives the constant 5. The assumptions already imply that A is positive semidefinite. They allow a singular center, singular endpoints, the empty index type, and zero Hessian; in the last case the third derivative is zero. A and B need not commute. Indeed, the congruences E(A+B)E and E(A-B)E are positive semidefinite. Trace cyclicity gives |Re Tr(B E^2)|<=Re Tr(A E^2), and the derivative formulas and the triangle inequality give the result.

**Definition 1.4 (A dimension independent constant).**

Lean statement: `D5/S3/Quantum/Matrix/HsfCubicRadial.UniversalCubicBound`

*Formalization.* `D5/S3/Quantum/Matrix/HsfCubicRadial.UniversalCubicBound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

UniversalCubicBound(C) means that for every natural dimension m, PSD A, Hermitian B, PSD endpoints A+B and A-B, and real |k|<=1, the actual derivatives obey |f'''(0)|<=C f''(0).

**Theorem 1.5 (The sharp uniform constant).**

Lean statement: `D5/S3/Quantum/Matrix/HsfCubicRadial.universal_constant_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/HsfCubicRadial.universal_constant_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every real C, UniversalCubicBound(C) holds if and only if C>=5. Sufficiency follows from the general matrix estimate. Necessity already follows in dimension one from A=1, B=-1, k=1, for which the Hessian is 24 and the third derivative is -120. The center is positive definite and one endpoint is singular. Consequently 5 cannot be improved even if the class is restricted to positive definite centers.

This is the normalized matrix-pencil result for alpha=3 and the radial second-variable restriction of the He-Saunderson-Fawzi question, Operator convexity along lines, self-concordance, and sandwiched Renyi entropies: arXiv:2502.05627v1, Conjecture 6.2; DOI 10.1007/s10107-025-02314-0, Conjecture 1. A fixed congruence motivates this normalization. An equality with the physical CFC-power expression is not proved here. General second-variable directions and exponents above 3 remain outside this theorem. The full conjecture remains open. No originality or official acceptance is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/HsfCubicRadial.UniversalCubicBound`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfCubicRadial.cubicRadialTrace`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfCubicRadial.cubic_derivatives`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfCubicRadial.cubic_radial_compatibility`
- Truth anchor: `D5/S3/Quantum/Matrix/HsfCubicRadial.universal_constant_iff`
