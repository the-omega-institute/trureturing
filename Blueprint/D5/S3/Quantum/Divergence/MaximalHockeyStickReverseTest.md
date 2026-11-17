# Actual finite density-matrix preparations and their profiles

## Abstract

Actual finite density-matrix preparations and their profiles

The source class is all k in the natural numbers and all ReverseTest A B k. Its weights need not have unit mass. Density states, rather than arbitrary positive components, ensure an actual CPTP preparation on the entire source matrix algebra. Empty matrix dimension does not assume a density state exists.

**Definition 1.1 (ReverseTest).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.ReverseTest`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.ReverseTest` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

A ReverseTest A B k gives nonnegative p,q on Fin k, one actual DensityState n for each label, and exact preparation sums for A and B. The operational infima, quadratic minimum and general-convex finiteCost all quantify over this unchanged structure.

**Definition 1.2 (stateMatrix).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.stateMatrix`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.stateMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

stateMatrix R i is the ordinary complex matrix underlying the density state at label i. It is PSD with trace one and is used by preparedOverlap and the mass calculations.

**Theorem 1.3 (cptp realization).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.cptp_realization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.cptp_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

Every ReverseTest is realized by a quantum channel from matrices on Fin k to matrices on n. The same CPTP map sends diag(p) to A and diag(q) to B. This is a realization theorem for actual states, not an assumption about an arbitrary L1 source.

**Definition 1.4 (preparedOverlap).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.preparedOverlap`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.preparedOverlap` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

preparedOverlap R t is the sum of min(p_i,t q_i) times the prepared state matrices. It is the actual common overlap induced by this test.

**Definition 1.5 (hockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.hockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.hockey` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

hockey R t is the actual classical sum of max(p_i-t q_i,0). Operational.operationalHockey takes its infimum over every finite alphabet; no SDP formula is built into this definition.

**Theorem 1.6 (overlap feasible).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.overlap_feasible`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.overlap_feasible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For t>=0, preparedOverlap R t is PSD and below A and tB. Positive component sums prove each of the three Loewner inequalities. maximal_hockey_le consumes this feasible point.

**Theorem 1.7 (maximal hockey le).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.maximal_hockey_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.maximal_hockey_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every actual finite test and t>=0, maximalHockey A B t <= hockey R t. The trace-one states identify the classical overlap mass and the feasible overlap bounds its SDP value. Operational combines this bound with the three-component witness to prove equality of the true infimum.

**Definition 1.8 (starCost).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.starCost`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.starCost` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

starCost R sums the standard closed quadratic perspectives over exactly the same labels. QuadraticBound and QuadraticIntegral compute and bound this actual cost.

**Definition 1.9 (maximalQuadratic).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.maximalQuadratic`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.maximalQuadratic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

maximalQuadratic A B is the EReal infimum of starCost over all k and actual ReverseTest A B k. There is no alphabet bound or minimizing-test premise.

**Theorem 1.10 (maximal quadratic le test).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.maximal_quadratic_le_test`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.maximal_quadratic_le_test` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

Every actual finite test gives an upper bound for maximalQuadratic by membership in its defining infimum. QuadraticCanonical consumes this bound with the attained spectral test.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.ReverseTest`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.cptp_realization`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.hockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.maximalQuadratic`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.maximal_hockey_le`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.maximal_quadratic_le_test`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.overlap_feasible`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.preparedOverlap`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.starCost`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickReverseTest.stateMatrix`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickProfile](MaximalHockeyStickProfile.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickQuadratic](MaximalHockeyStickQuadratic.md)
- Dependency: [D5/S3/Quantum/Foundation/FinitePreparationChannel](../Foundation/FinitePreparationChannel.md)
