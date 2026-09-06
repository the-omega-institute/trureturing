# Conflict Repairs Are Hitting Sets

## Abstract

Every successful downward-closed conflict repair intersects every conflicting core contained in the original rights.

**Definition 1.1 (A minimal conflict has only satisfiable proper subsets).**

$$\forall Right \in Type, Satisfiable \in \operatorname{Set}\left(Right\right) \to Prop, core \in \operatorname{Set}\left(Right\right),\; \operatorname{MinimalConflictCore}\left(Satisfiable, core\right) \Leftrightarrow \left(\left(\neg Satisfiable\left(core\right)\right) \land \left(\forall smaller \in \operatorname{Set}\left(Right\right),\; smaller \subset core \Rightarrow Satisfiable\left(smaller\right)\right)\right)$$

*Formalization.* `D5/S3/ConceptDynamics/Rights/ConflictRepairHittingSet.MinimalConflictCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a satisfiability predicate on sets of rights, a core is minimally conflicting exactly when the core itself is unsatisfiable and every proper subset of it is satisfiable.

**Theorem 1.2 (A successful repair hits a conflict core).**

$$\forall Right \in Type, Satisfiable \in \operatorname{Set}\left(Right\right) \to Prop, rights \in \operatorname{Set}\left(Right\right), modified \in \operatorname{Set}\left(Right\right), core \in \operatorname{Set}\left(Right\right),\; \left(\operatorname{DownwardClosed}\left(Satisfiable\right) \land \left(core \subseteq rights \land \left(\left(\neg Satisfiable\left(core\right)\right) \land Satisfiable\left(\operatorname{difference}\left(rights, modified\right)\right)\right)\right)\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{intersection}\left(modified, core\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Rights/ConflictRepairHittingSet.repair_must_hit_conflict_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume satisfiability is preserved when rights are removed. If a conflicting core lies inside the original rights and deleting the modified rights leaves a satisfiable remainder, then at least one modified right belongs to that core.

Indeed, if the modification missed the core, the entire core would remain inside the repaired set. Downward closure would then make the core satisfiable, contradicting its conflict. Neither finiteness nor minimality of the core is required.

**Lemma 1.3 (A successful repair hits every conflict core).**

$$\forall Right \in Type, Satisfiable \in \operatorname{Set}\left(Right\right) \to Prop, rights \in \operatorname{Set}\left(Right\right), modified \in \operatorname{Set}\left(Right\right), core \in \operatorname{Set}\left(Right\right),\; \left(\operatorname{DownwardClosed}\left(Satisfiable\right) \land \left(Satisfiable\left(\operatorname{difference}\left(rights, modified\right)\right) \land \left(core \subseteq rights \land \left(\neg Satisfiable\left(core\right)\right)\right)\right)\right) \Rightarrow \operatorname{Nonempty}\left(\operatorname{intersection}\left(modified, core\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Rights/ConflictRepairHittingSet.repair_hits_every_conflict_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a modification whose removal makes the original rights satisfiable. For every unsatisfiable subset of the original rights, the single-core obstruction forces a nonempty intersection with the modification. Thus one successful repair is a hitting set for the entire family of conflict cores present in the original rights.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Rights/ConflictRepairHittingSet.MinimalConflictCore`
- Truth anchor: `D5/S3/ConceptDynamics/Rights/ConflictRepairHittingSet.repair_hits_every_conflict_core`
- Truth anchor: `D5/S3/ConceptDynamics/Rights/ConflictRepairHittingSet.repair_must_hit_conflict_core`
