# The bounded quadratic hockey reference

## Abstract

A finite triangle integral represents the standard quadratic closed perspective and actual test cost.

**Theorem 1.1 (Exact scalar reference, including both axes).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.star_perspective_hockey_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.star_perspective_hockey_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For p,q >= 0, the standard perspective (p-q)^2/(p+q), with value zero at the origin, is q-3p plus eight times the integral of max(p-u(p+q),0) over 0 <= u <= 1. The proof integrates the linear triangle up to p/(p+q) and treats p=q=0 separately. This is the closed perspective of f_*(s)=(s-1)^2/(s+1).

**Theorem 1.2 (The actual reverse-test cost identity).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.star_cost_hockey_integral`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.star_cost_hockey_integral` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

Summing the scalar identity over the actual finite labels gives starCost = Tr B - 3 Tr A + 8 integral compactHockey. For 0<u<1, compactHockey is exactly (1-u) times the original classical hockey profile at t=u/(1-u). No improper integral or unproved identification with another cost is used.

**Definition 1.3 (The actual compact-coordinate classical profile).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compactHockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compactHockey` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

compactHockey R u is sum max(p_i-u(p_i+q_i),0) over the original labels of R, for every real u. It is the bounded-interval profile integrated in the exact quadratic cost formula.

**Theorem 1.4 (Continuity on the entire real line).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compact_hockey_continuous`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compact_hockey_continuous` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For any actual finite test, compactHockey R is continuous on all real u. It is a finite sum of maxima of affine functions. QuadraticEquality uses this continuity to detect a nonzero gap on a neighbourhood.

**Theorem 1.5 (Exact return to positive thresholds).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compact_hockey_eq_scaled`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compact_hockey_eq_scaled` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For an actual finite test and 0<u<1, compactHockey R u=(1-u) hockey R (u/(1-u)). The proof factors the positive coefficient 1-u through each positive part. QuadraticEquality transports the compact gap to the original positive-threshold profile with this identity.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compactHockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compact_hockey_continuous`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.compact_hockey_eq_scaled`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.star_cost_hockey_integral`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral.star_perspective_hockey_integral`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate](MaximalHockeyStickApproximate.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticCanonical](MaximalHockeyStickQuadraticCanonical.md)
