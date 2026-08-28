# Loyalty Cannot Repair Underexpression

## Abstract

A mandate-loyal representation can remain pointwise insufficient when the mandate collapses states with different targets.

**Lemma 1.1 (A mandate collision defeats every loyal representation).**

$$\forall X \in Type, B \in Type, Y \in Type, M \in X \to B, T \in X \to Y, J \in X \to Y,\; \operatorname{RepresentationLoyal}\left(M, J\right) \Rightarrow \left(\left(\exists x \in X, y \in X,\; M\left(x\right) = M\left(y\right) \land T\left(x\right) \ne T\left(y\right)\right) \Rightarrow \left(\neg \operatorname{RepresentationSufficient}\left(J, T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/LoyaltyCannotRepairUnderexpression.loyal_representation_fails_under_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A representation is loyal when it factors through the mandate map. It is therefore constant on every mandate fiber, regardless of which factor map is chosen.

If two states share a mandate value but have different target values, no loyal representation can agree with the target at both states. Thus a single underexpressed fiber rules out pointwise sufficiency on the whole state space.

**Theorem 1.2 (Loyalty does not imply target sufficiency).**

$$\exists M \in Bool \to Unit, T \in Bool \to Bool, J \in Bool \to Bool,\; \operatorname{RepresentationLoyal}\left(M, J\right) \land \left(\left(\exists x \in Bool, y \in Bool,\; M\left(x\right) = M\left(y\right) \land T\left(x\right) \ne T\left(y\right)\right) \land \left(\neg \operatorname{RepresentationSufficient}\left(J, T\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Representation/LoyaltyCannotRepairUnderexpression.loyalty_cannot_repair_underexpression` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take Boolean states and let the mandate forget the state completely by mapping both values to the unique element of Unit. Let the target be the Boolean identity and let the representation be constantly false.

The constant representation factors through the one-point mandate, so it is fully loyal. Yet true and false lie in the same mandate fiber while the target distinguishes them, and the representation misses the target at true. This concrete witness separates loyalty from sufficiency.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Representation/LoyaltyCannotRepairUnderexpression.loyal_representation_fails_under_collision`
- Truth anchor: `D5/S3/ConceptDynamics/Representation/LoyaltyCannotRepairUnderexpression.loyalty_cannot_repair_underexpression`
- Dependency: [D5/S3/ConceptDynamics/Decision/MixedFiberZeroErrorImpossible](../Decision/MixedFiberZeroErrorImpossible.md)
- Dependency: [D5/S3/ConceptDynamics/NormativeStructure/HistorySensitiveOutcomeReductionObstruction](../NormativeStructure/HistorySensitiveOutcomeReductionObstruction.md)
