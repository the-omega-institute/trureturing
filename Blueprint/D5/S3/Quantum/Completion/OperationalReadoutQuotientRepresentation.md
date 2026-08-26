# Operational Readout Quotient Representation

## Abstract

Operational state classes are canonically and affinely represented by realized readouts.

**Theorem 1.1 (The operational quotient is canonically its readout range).**

$$\begin{gathered}\forall d: \operatorname{Type}, \operatorname{Fintype}(d) \land \operatorname{DecidableEq}(d) \Rightarrow\\{}\forall S: \operatorname{MatrixOperatorSystem}(d),\\{}r_{S} := \operatorname{operatorSystemReadout}(S), E_{S} := \operatorname{quotientKerEquivRange}(r_{S}): \operatorname{Quotient}(\operatorname{ker}(r_{S})) \equiv \operatorname{range}(r_{S}),\\{}{\forall \rho: \operatorname{DensityState}(d), E_{S}(\operatorname{class}(\rho)) = \operatorname{rangePoint}(r_{S}(\rho))} \land\\{}{\forall EPrime: \operatorname{Quotient}(\operatorname{ker}(r_{S})) \equiv \operatorname{range}(r_{S}), {\forall \rho: \operatorname{DensityState}(d), EPrime(\operatorname{class}(\rho)) = \operatorname{rangePoint}(r_{S}(\rho))} \Rightarrow EPrime = E_{S}} \land\\{}\forall t: \mathbb{R}, \rho: \operatorname{DensityState}(d), \Sigma: \operatorname{DensityState}(d), 0 \leq t \leq 1 \Rightarrow\\{}\exists ! \rho_{t}: \operatorname{DensityState}(d), \operatorname{matrix}(\rho_{t}) = t \cdot \operatorname{matrix}(\rho) + {1 - t} \cdot \operatorname{matrix}(\Sigma) \land\\{}\operatorname{value}(E_{S}(\operatorname{class}(\rho_{t}))) = t \cdot \operatorname{value}(E_{S}(\operatorname{class}(\rho))) + {1 - t} \cdot \operatorname{value}(E_{S}(\operatorname{class}(\Sigma))).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/OperationalReadoutQuotientRepresentation.operational_readout_quotient_representation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Density states are identified exactly when every effect in the chosen operator system has the same trace expectation.

The named kernel-range equivalence sends each state class to its realized readout and is uniquely determined by this rule.

Positive trace-one matrices are closed under binary mixtures. Trace linearity then shows that the canonical equivalence preserves every such convex combination pointwise.

## References

- Truth anchor: `D5/S3/Quantum/Completion/OperationalReadoutQuotientRepresentation.operational_readout_quotient_representation`
- Dependency: [D5/S3/Quantum/Fibers/FutureStatisticsEquivalence](../Fibers/FutureStatisticsEquivalence.md)
