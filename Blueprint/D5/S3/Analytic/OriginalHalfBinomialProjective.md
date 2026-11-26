# The native period-ratio Schwarzian

## Abstract

The literal original complementary period ratio has a nonzero derivative and an exact Schwarzian on the entire open lens.

**Theorem 1.1 (Actual third-order regularity and exact Schwarzian).**

Lean statement: `D5/S3/Analytic/OriginalHalfBinomialProjective.original_tau_projective`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/OriginalHalfBinomialProjective.original_tau_projective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Frank W. J. Olver, Daniel W. Lozier, Ronald F. Boisvert, and Charles W. Clark, editors (2010). *NIST Digital Library of Mathematical Functions: Schwarzian derivatives and the hypergeometric differential equation*. URL: <https://dlmf.nist.gov/1.13>.

*Commentary.*

For every complex r with norm r<1 and norm(1-r)<1, let P be the literal original half-binomial-square period and tau(r)=iP(1-r)/P(r), exactly as defined in OriginalHalfBinomialWronskian. Its actual derivative is nonzero. The theorem gives an actual derivative of tau', differentiability of tau'', and g=tau''/tau'=-(1-2r)/(r(1-r))-2P'/P. It proves S(tau)=(1-r+r squared)/(2r squared(1-r) squared).

The generic inference is instantiated with A=r(1-r), p=(1-2r)/A, q=-1/(4A), W=-i/(pi A), y=P and the actual tau. The native Picard-Fuchs theorem provides both differentiability conclusions and the ODE. The proved disk nonvanishing and the lens inequalities exclude all denominator zeros. Rational differentiation proves W'=-pW internally; the existing exact tau derivative identifies W/P squared. No extra ODE, regularity or nonvanishing hypotheses are imposed at the endpoint.

The canonical FiniteMode Gaussian period correction consumes the actual quotient formula. This local result does not assert continuation, monodromy, global uniformization, positivity, operator transport or a physical geometry.

## References

- Truth anchor: `D5/S3/Analytic/OriginalHalfBinomialProjective.original_tau_projective`
- Dependency: [D5/S3/Analytic/AbelRatioSchwarzian](AbelRatioSchwarzian.md)
- Dependency: [D5/S3/Analytic/OriginalHalfBinomialWronskian](OriginalHalfBinomialWronskian.md)
