# Redundant Appeal and Defect Persistence

## Abstract

Record-determined appeal evidence cannot repair a target defect.

**Definition 1.1 (Concept equivalence is mutual refinement).**

$$\forall X, C, D: \operatorname{Type}, left: X \to C, right: X \to D,\\{}\operatorname{ConceptEquivalent}(left, right) \iff \operatorname{Refines}(left, right) \land \operatorname{Refines}(right, left).$$

*Formalization.* `D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence.ConceptEquivalent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two readouts on the same source are concept-equivalent exactly when the left readout factors through the right and the right factors through the left.

**Theorem 1.2 (Record-determined appeal evidence cannot repair a defect).**

$$C: X \to B_{C}, A: X \to B_{A}, T: X \to Y,\\{}\operatorname{Refines}(Q, R) \iff \exists f, Q = \operatorname{compose}(f, R),\\{}\operatorname{join}(C, A)(x) = (C(x), A(x)),\\{}\operatorname{Defect}(Q, T) = \{(x, y) \mid Q(x) = Q(y) \land T(x) \neq T(y)\},\\{}\operatorname{Refines}(A, C) \Rightarrow\\{}(\operatorname{ConceptEquivalent}(\operatorname{join}(C, A), C)) \land\\{}(\forall x, y, \operatorname{join}(C, A)(x) = \operatorname{join}(C, A)(y) \iff C(x) = C(y)) \land\\{}(\operatorname{Defect}(C, T) \neq \emptyset \Rightarrow (\operatorname{Defect}(\operatorname{join}(C, A), T) \neq \emptyset \land \neg\operatorname{Refines}(T, \operatorname{join}(C, A)))).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence.redundant_appeal_cannot_repair_structural_defect` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original case record C, permitted appeal evidence A, and authorized target T are independent readouts on the same case carrier. Refinement is the frozen family factorization order.

The appeal interface is constructed as the paired readout C join A. The target defect is the set of case pairs identified by a readout but distinguished by T; full appeal capability means T factors through the paired interface.

When A factors through C, the join universal property gives mutual refinement of C join A and C. Applying the appeal factor to equal record values proves that their indistinguishability relations are equal, so the appeal adds no case distinctions.

Any original target-defect pair therefore remains a defect pair after the appeal join. Such a pair contradicts every proposed target factor, showing that re-review of the same coarse record does not supply full appeal capability.

Repository search found no theorem packaging all four public clauses. The proof directly imports and applies the frozen concept-family primitives and Mathlib equality transport.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence.ConceptEquivalent`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence.redundant_appeal_cannot_repair_structural_defect`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
