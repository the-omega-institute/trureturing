# Integrated quadratic equality for singular finite pairs

## Abstract

The actual quadratic infimum equals its integrated maximal hockey reference exactly at the common-interior commutator criterion.

**Theorem 1.1 (The actual infimum and the original matrix pair).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.quadratic_integrated_eq_iff_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.quadratic_integrated_eq_iff_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every finite positive semidefinite pair A,B, put S=A+B, C=normalize(S,A) and P=interiorProjection(C). The infimum over all actual finite reverse tests for f_*(s)=(s-1)^2/(s+1) equals quadraticHockeyValue exactly when PSP commutes with PCP. The proof uses the actual spectral test, the exact compact hockey integral, positivity and continuity of its gap, and original_all_thresholds_iff_commute. Singular, zero and empty matrix spaces are included.

**Theorem 1.2 (Actual approximate tests transfer to the quadratic reference).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.vanishing_curvature_gaps_imply_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.vanishing_curvature_gaps_imply_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For any sequence of actual finite reverse tests, integrable gaps whose integrals tend to zero against a locally finite measure positive on every nonempty open set force the same original common-interior commutator to vanish. Pointwise gap convergence and dominated convergence on (0,1) transfer the costs to the actual quadratic minimum. This theorem assumes the vanishing gap integrals explicitly. It does not establish the general convex Stieltjes representation, its finite-cost approximation, or the full all-convex divergence equality classification.

**Definition 1.3 (The compact-coordinate PSD maximal profile).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.compactMaximal`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.compactMaximal` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

compactMaximal A B u=(1-u) maximalHockey A B (u/(1-u)). The relevant interval is 0<u<1; the definition alone does not impose that interval. The integrated quadratic criterion uses this profile with endpoint measure-zero handling.

**Definition 1.4 (The bounded quadratic hockey value).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.quadraticHockeyValue`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.quadraticHockeyValue` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

quadraticHockeyValue A B is Tr(B)-3 Tr(A) plus eight times the real interval integral of compactMaximal A B over [0,1]. It is the actual maximal hockey reference for the standard quadratic generator in finite dimension. The exact operational identification of its PSD profile is supplied by Operational.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.compactMaximal`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.quadraticHockeyValue`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.quadratic_integrated_eq_iff_commute`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticEquality.vanishing_curvature_gaps_imply_commute`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickQuadraticIntegral](MaximalHockeyStickQuadraticIntegral.md)
