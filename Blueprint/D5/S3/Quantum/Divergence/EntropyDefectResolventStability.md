# Entropy defect and resolvent stability

## Abstract

Quantum entropy loss controls supported resolvent intertwining.

**Theorem 1.1 (A quartic error bound without faithful physical states).**

Lean statement: `D5/S3/Quantum/Divergence/EntropyDefectResolventStability.entropy_defect_resolvent_stability`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/EntropyDefectResolventStability.entropy_defect_resolvent_stability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alex Meiburg (2026). *Uniform power-slope control for singular relative-entropy limits*. URL: <https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/Entropy/Relative.lean>.

*Commentary.*

For an arbitrary finite quantum channel and density states with input support containment, construct the existing canonical supported relative-modular model M. At every positive shift t, let w be the difference between (A+tI) inverse applied to the normalized input vector and V applied to (B+tI) inverse of the output vector. Then t^4 times the square of the squared L2 norm of w is at most four times the actual finite trace-log relative-entropy loss. Positivity is used only on the support carriers, so singular physical states are included.

The proof reuses the canonical supported model, the spectral quadratic-form expansion and the saturated resolvent energy bound. The new finite-calculus step expands the shifted logarithmic difference F in positive spectral points with nonnegative unit-mass weights. Its derivative G is nonnegative and its limit at infinity is zero. The reciprocal inequality G(s) >= G(t) - (s-t)/t^2 makes F(s) - G(t)(s-t) + (s-t)^2/t^2 monotone for s >= t. Evaluate at s=t+G(t)t^2/2 and use F(0) <= F(t) <= F(s) <= 0. This bounds t^2 G(t)^2 by four times the entropy loss; the existing energy inequality t times norm squared of w <= G(t) gives the claimed quartic estimate. This is a repository derivation from finite spectral calculus and existing suppliers. It supplies no trace-distance recovery estimate or claim of literature novelty.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/EntropyDefectResolventStability.entropy_defect_resolvent_stability`
- Dependency: [D5/S3/Quantum/Divergence/CanonicalRelativeModularModel](CanonicalRelativeModularModel.md)
- Dependency: [D5/S3/Quantum/Divergence/ResolventFunctionalRigidity](ResolventFunctionalRigidity.md)
