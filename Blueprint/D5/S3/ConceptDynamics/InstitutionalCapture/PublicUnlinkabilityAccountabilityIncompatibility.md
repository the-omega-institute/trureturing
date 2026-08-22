# Public Unlinkability and Accountability Incompatibility

## Abstract

Nontrivial identity makes public unlinkability incompatible with complete accountability.

**Theorem 1.1 (Public unlinkability and complete accountability are incompatible).**

$$\forall X, B_{P}, B_{I}: \operatorname{Type},\\{}P: X \to B_{P}, I: X \to B_{I},\\{}{\exists x, y: X, \operatorname{I}(x) \neq \operatorname{I}(y)} \Rightarrow\\{}\neg {\operatorname{commonCoreRelation}(P, I) = top \land \operatorname{Refines}(I, P)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/InstitutionalCapture/PublicUnlinkabilityAccountabilityIncompatibility.public_unlinkability_accountability_incompatible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let P be a public transcript and I an identity readout on the same source carrier. Identity is nontrivial when two source states have different identity readouts.

Structural public unlinkability says the canonical common-core relation of P and I is the top setoid, so its common coarsening is trivial. Complete public accountability says I factors through P via the canonical Refines relation.

The displayed conclusion publicly negates the conjunction of these two clauses. It imports the existing common-core construction and applies its obstruction theorem without redeclaring either family primitive.

## References

- Truth anchor: `D5/S3/ConceptDynamics/InstitutionalCapture/PublicUnlinkabilityAccountabilityIncompatibility.public_unlinkability_accountability_incompatible`
