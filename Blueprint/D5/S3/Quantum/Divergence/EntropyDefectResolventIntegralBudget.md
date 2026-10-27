# Entropy defect and integrated resolvent stability

## Abstract

Quantum entropy loss pays for the full supported resolvent energy integral.

**Theorem 1.1 (The full positive-axis energy budget).**

Lean statement: `D5/S3/Quantum/Divergence/EntropyDefectResolventIntegralBudget.entropy_defect_resolvent_integral_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/EntropyDefectResolventIntegralBudget.entropy_defect_resolvent_integral_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

For an arbitrary channel between finite nonempty quantum systems and density states rho and sigma with support of rho contained in support of sigma, form the canonical supported relative-modular model M. For positive t, let w(t) be (A+tI) inverse applied to xi minus V applied to (B+tI) inverse of eta. The real function t times the real part of star(w(t)) dot w(t) is integrable over the entire positive real axis. Its integral is at most the finite trace-log relative entropy of rho and sigma minus that of their channel images. The dot product is the squared L2 norm, expressed as the sum of squared coordinate norms; no supremum norm is substituted. Physical density matrices may be singular.

In the spectral coordinates of A and B, the distinguished vectors give weights u and v of total mass one on positive spectral points p and q. Set F(t) to the weighted sum of log(t+p) minus the weighted sum of log(t+q). Its derivative G(t) is the difference of the corresponding weighted resolvents. Equal total mass cancels log(t), so F tends to zero at infinity. The saturated resolvent energy inequality makes G nonnegative and bounds the actual energy by G. The nonnegative-derivative improper fundamental theorem therefore proves that G is integrable and its integral is minus F(0). The canonical trace identities identify this value with the actual entropy loss. Continuity of shifted matrix inversion gives measurability of the energy; domination gives its integrability and the integral bound. This derivation asserts no trace-distance recovery estimate or literature novelty.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/EntropyDefectResolventIntegralBudget.entropy_defect_resolvent_integral_budget`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Divergence/ResolventFunctionalRigidity](ResolventFunctionalRigidity.md)
