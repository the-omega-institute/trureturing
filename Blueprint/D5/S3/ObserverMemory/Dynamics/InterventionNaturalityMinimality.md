# Intervention Naturality Minimality

## Abstract

Naturality on every nonempty address type forces transition commutation and the minimal controlled behavior factor.

**Theorem 1.1 (Intervention naturality forces the minimal behavior factor).**

$$\begin{gathered}(\forall u, \operatorname{DiagonalNatural}(r, F(u), G(u))) \Rightarrow\\(\forall u, r \circ F(u) = G(u) \circ r) \land\\(\exists! h: W \to Z, \operatorname{Surjective}(h) \land \pi = h \circ r).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Dynamics/InterventionNaturalityMinimality.intervention_naturality_minimality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let a finite controlled state carrier Y map surjectively to a finite realization W while preserving its current readout. Assume that pointwise projection commutes with every input-indexed twisted diagonal for every nonempty address type and every table.

Specializing the address type to Unit and the sole table entry to an arbitrary state recovers each transition equation. The theorem then applies the existing controlled-behavior universal property to obtain the unique surjective factor from W to the complete behavior quotient, including its projection, update, and readout equations.

Pinned Mathlib supplies Function.semiconj_iff_comp_eq for converting the singleton calculation to a function equation. Repository search supplied controlled_behavior_universal_property for the quotient conclusion; both declarations are applied directly.

## References

- Truth anchor: `D5/S3/ObserverMemory/Dynamics/InterventionNaturalityMinimality.intervention_naturality_minimality`
- Dependency: [D5/S0/Diagonal/Naturality/CoordinateRestrictionNaturality](../../../S0/Diagonal/Naturality/CoordinateRestrictionNaturality.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](../Prediction/ControlledBehaviorUniversality.md)
