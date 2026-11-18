# Uniform bounds for actual finite-test gaps

## Abstract

Uniform bounds for actual finite-test gaps

The same fixed pair A,B supplies every test in a sequence. Constants depend only on its actual traces, not the number of labels. This source feeds the full-support measure transfer and the general-convex finite-cost approximation argument.

**Definition 1.1 (PositiveThreshold).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.PositiveThreshold`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.PositiveThreshold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

PositiveThreshold is the real subtype t>0. This is exactly the curvature domain used in the integrated classification.

**Definition 1.2 (gap).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.gap`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.gap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

gap R t=hockey R t-maximalHockey A B t for positive t. This is the actual gap of the prepared classical test against the PSD value, whose operational meaning is proved in Operational.

**Theorem 1.3 (left mass).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.left_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.left_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every actual finite test, Re Tr(A)=sum p_i, because each prepared state has trace one. Both orientation conversion and cost decomposition consume the original mass identity.

**Theorem 1.4 (right mass).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.right_mass`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.right_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every actual finite test, Re Tr(B)=sum q_i. The original arbitrary mass is retained in Lipschitz constants and affine cost decomposition.

**Theorem 1.5 (maximal hockey nonneg).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.maximal_hockey_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.maximal_hockey_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B and t>=0, maximalHockey A B t>=0. Every feasible overlap is bounded by A in trace. The compact maximal profile and general convex kernel use this bound.

**Theorem 1.6 (hockey le trace).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.hockey_le_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.hockey_le_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every test and t>=0, hockey R t<=Re Tr(A). Nonnegativity of p,q bounds each positive part by p_i. The actual gap bound uses this uniform mass ceiling.

**Theorem 1.7 (hockey lipschitz).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.hockey_lipschitz`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.hockey_lipschitz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every test and all real s,t, |hockey R t-hockey R s|<=|t-s| Re Tr(B). Summing the scalar positive-part Lipschitz estimates removes dependence on label count. actual_gap_profile_data consumes it.

**Theorem 1.8 (actual gap profile data).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.actual_gap_profile_data`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.actual_gap_profile_data` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B, on positive thresholds gap R lies in [0,Tr(A)] and is Lipschitz with constant 2 Tr(B), expressed by Real.toNNReal. Combining overlap and classical Lipschitz bounds gives constants uniform over every finite test. Both quadratic and general convex transfer consume these facts.

**Theorem 1.9 (actual tests full support transfer).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.actual_tests_full_support_transfer`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.actual_tests_full_support_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B, any sequence of actual finite tests, and g_j exactly equal to their gaps, assume integrable gaps whose integrals against locally finite full-support mu tend to zero. Then g_j(t) tends to zero at every positive threshold and its integral tends to zero against every finite measure nu. No minimizing test or compactness of the test class is assumed. QuadraticEquality.vanishing_curvature_gaps_imply_commute consumes this transfer.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.PositiveThreshold`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.actual_gap_profile_data`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.actual_tests_full_support_transfer`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.gap`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.hockey_le_trace`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.hockey_lipschitz`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.left_mass`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.maximal_hockey_nonneg`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate.right_mass`
- Dependency: [D5/S3/Analytic/Measure/FullSupportProfileTransfer](../../Analytic/Measure/FullSupportProfileTransfer.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest](MaximalHockeyStickReverseTest.md)
