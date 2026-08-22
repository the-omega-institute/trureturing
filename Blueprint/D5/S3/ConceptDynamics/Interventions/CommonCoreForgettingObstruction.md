# Common Core Forgetting Obstruction

## Abstract

A nontrivial safety-blame core prevents safety-preserving complete blame erasure.

**Definition 1.1 (Common core relation).**

Lean statement: `D5/S3/ConceptDynamics/Interventions/CommonCoreForgettingObstruction.commonCoreRelation`

*Formalization.* `D5/S3/ConceptDynamics/Interventions/CommonCoreForgettingObstruction.commonCoreRelation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The common core relation of two concept readouts is the join of their kernel setoids, the least equivalence relation containing both indistinguishability relations.

The quotient by this relation is the greatest common coarsening in the canonical concept factorization order.

**Theorem 1.2 (Nontrivial common core obstructs complete forgetting).**

$$\forall X, B_{S}, B_{B}, B_{F}: \operatorname{Type},\\{}S: X \to B_{S}, B: X \to B_{B}, F: X \to B_{F},\\{}\operatorname{commonCoreRelation}(S, B) \neq top \Rightarrow\\{}\neg {\operatorname{Refines}(S, F) \land \operatorname{commonCoreRelation}(F, B) = top}.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/CommonCoreForgettingObstruction.common_core_obstructs_complete_forgetting` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Safety, blame, and future availability are independent concept readouts on the same source carrier. Refinement is the canonical frozen family factorization relation.

A common core is trivial exactly when its kernel join is the top setoid, which identifies every pair of source states. Thus the public conclusion negates safety preservation and complete blame erasure as a simultaneous pair of clauses.

A safety factor through the future readout makes the future kernel no larger than the safety kernel. Joining both with the blame kernel preserves this order, so a top future-blame core would force the safety-blame core to be top as well.

The common core is constructed from the two source kernels before the impossibility claim; it is not defined by the theorem's target.

Repository search found no exact obstruction theorem. The proof directly imports the canonical concept carrier and refinement relation and applies the pinned setoid complete-lattice operations.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/CommonCoreForgettingObstruction.commonCoreRelation`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/CommonCoreForgettingObstruction.common_core_obstructs_complete_forgetting`
