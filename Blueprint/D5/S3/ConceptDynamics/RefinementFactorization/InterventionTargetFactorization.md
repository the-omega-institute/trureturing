# Intervention Target Factorization

## Abstract

Allowed-intervention law kernels characterize unique target descent through the realized causal image.

**Theorem 1.1 (The causal image carries exactly the identifiable targets).**

$$\begin{gathered}\forall A, M, Y: \operatorname{Type},\\{}L: A \to \operatorname{Type},\\{}law: \forall a: A, M \to L_{a},\\{}T: M \to Y,\\{}(\exists! f: \operatorname{range}(\operatorname{jointReadout}(law)) \to Y, T = f \circ \operatorname{rangeFactorization}(\operatorname{jointReadout}(law))) \Leftrightarrow (\operatorname{ker}(\operatorname{jointReadout}(law)) \subseteq \operatorname{ker}(T)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/RefinementFactorization/InterventionTargetFactorization.intervention_target_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each allowed intervention supplies a law-valued readout on the same model carrier. The canonical joint readout constructs their complete dependent profile, and its realized range is the causal image named in the theorem.

Kernel containment says that models with the same complete intervention profile must have the same target value. The public statement exposes the resulting unique factor and its commuting equation directly on that realized image.

The pinned realized-image representative chooses a source model for each profile in the causal image. Kernel containment makes the resulting target value representative-independent, while surjectivity of the canonical range map proves uniqueness.

## References

- Truth anchor: `D5/S3/ConceptDynamics/RefinementFactorization/InterventionTargetFactorization.intervention_target_factorization`
- Dependency: [D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion](../Faithfulness/JointFaithfulnessLeibnizCriterion.md)
