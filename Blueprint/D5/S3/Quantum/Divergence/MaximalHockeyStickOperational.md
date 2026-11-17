# The finite operational hockey infima equal the PSD overlap formulas

## Abstract

The finite operational hockey infima equal the PSD overlap formulas

The two formulas are the finite-matrix content of HMT Proposition V.1 (V.124)-(V.125), following Matsumoto. They are known antecedents, not new conjecture solutions. Only actual finite ReverseTest alphabets are quantified here; identifying an arbitrary L1 source infimum requires a separate theorem. All pairs retain arbitrary traces, zero and singular matrices and empty dimension.

**Definition 1.1 (negativeHockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.negativeHockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.negativeHockey` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

negativeHockey R t is the actual sum max(t q_i-p_i,0). Convex.testKernel uses this negative orientation at 0<t<=1.

**Definition 1.2 (operationalHockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operationalHockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operationalHockey` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

operationalHockey A B t is the real infimum of hockey R t over all natural k and all ReverseTest A B k. Nonemptiness and attainment for PSD pairs and t>0 are proved by an actual witness.

**Definition 1.3 (operationalNegativeHockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operationalNegativeHockey`

*Formalization.* `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operationalNegativeHockey` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

operationalNegativeHockey uses exactly the same entire finite source class and the actual negative profile. The threshold-dependent three-component witness attains both orientations simultaneously.

**Theorem 1.4 (negative hockey eq).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.negative_hockey_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.negative_hockey_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every finite test and every real t, negativeHockey R t=hockey R t-Tr(A)+t Tr(B). The original mass identities and the scalar positive-part relation prove this. The negative infimum theorem consumes the conversion.

**Theorem 1.5 (reverse test attains hockey).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.reverse_test_attains_hockey`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.reverse_test_attains_hockey` (`✓ std3`). ∎

*Citation.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For PSD A,B and t>0, one actual finite test has hockey=maximalHockey and negativeHockey=t Tr(B)-overlapValue A (tB). Take an attained common PSD lower bound X and components X,A-X,tB-X. Independent Fin 3 labels use coefficients a=(1,1,0), b=(1/t,0,1/t); normalization gives the stated masses. Zero components have a coordinate state with zero weight. If dimension is empty, the witness has zero labels, so no density state or Nonempty n assumption is required. Both operational infimum equalities consume this witness.

**Theorem 1.6 (operational hockey eq).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operational_hockey_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operational_hockey_eq` (`✓ std3`). ∎

*Citation.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every finite PSD pair and t>0, the infimum of the actual positive classical profiles over all k and ReverseTest equals Tr(A)-overlapValue A (tB). The existing feasible-overlap lower bound and the attained three-component test give both inequalities. Convex.maximal_kernel_eq_operational consumes this formula.

**Theorem 1.7 (operational negative hockey eq).**

Lean statement: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operational_negative_hockey_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operational_negative_hockey_eq` (`✓ std3`). ∎

*Citation.* Fumio Hiai; Milan Mosonyi; Marco Tomamichel (2026). *Hockey stick f-divergences*. URL: <https://arxiv.org/abs/2607.08760v1>.

*Commentary.*

For every finite PSD pair and t>0, the infimum of the actual negative classical profiles over all k and ReverseTest equals t Tr(B)-overlapValue A (tB). The same test attains it; no separate source-class assumption is introduced. Convex uses this formula for the whole negative curvature branch, including the atom at one.

## References

- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.negativeHockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.negative_hockey_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operationalHockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operationalNegativeHockey`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operational_hockey_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.operational_negative_hockey_eq`
- Truth anchor: `D5/S3/Quantum/Divergence/MaximalHockeyStickOperational.reverse_test_attains_hockey`
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickApproximate](MaximalHockeyStickApproximate.md)
- Dependency: [D5/S3/Quantum/Divergence/MaximalHockeyStickComponents](MaximalHockeyStickComponents.md)
