# Branching Freedom Needs a Relation

## Abstract

A process with two distinct futures is not functional, and branching autonomy strictly strengthens autonomy.

**Theorem 1.1 (A branching process is not functional).**

$$\forall X \in \operatorname{Type}, F \in X \to \operatorname{Set}\left(X\right),\; \operatorname{BranchingFree}\left(F\right) \Rightarrow \left(\neg \left(\exists f \in X \to X,\; \forall a \in X,\; F\left(a\right) = \left\{f\left(a\right)\right\}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/BranchingFreedomNeedsRelation.branching_process_is_not_functional` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A branch supplies one state with two distinct possible successors. If the process were the graph of a deterministic function, membership in the corresponding singleton would identify both successors with the same function value.

The two successors would then be equal, contradicting the branch. Thus a genuinely branching transition process cannot be represented by any state-transition function.

**Lemma 1.2 (A functional process has no branch).**

$$\forall X \in \operatorname{Type}, f \in X \to X,\; \neg \operatorname{BranchingFree}\left(a \mapsto \left\{f\left(a\right)\right\}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/BranchingFreedomNeedsRelation.functional_process_is_not_branching` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The process induced by a function assigns each state the singleton containing its function value. Any two possible successors of the same state must therefore coincide, so no pair of distinct futures can witness branching.

**Lemma 1.3 (Branching freedom strictly strengthens autonomy).**

$$\left(\forall External \in \operatorname{Type}, X \in \operatorname{Type}, P \in External \to \left(X \to \operatorname{Set}\left(X\right)\right),\; \operatorname{BranchingAutonomousFree}\left(P\right) \Rightarrow \operatorname{AutonomousFree}\left(P\right)\right) \land \left(\exists P \in Bool \to \left(Bool \to \operatorname{Set}\left(Bool\right)\right),\; \operatorname{AutonomousFree}\left(P\right) \land \left(\neg \operatorname{BranchingAutonomousFree}\left(P\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Fibers/BranchingFreedomNeedsRelation.branching_freedom_strictly_stronger_than_autonomy` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Branching autonomy includes autonomy as one of its conditions, so every branching-autonomous process family is insensitive to at least two distinct external inputs.

The converse fails for the Boolean identity process, chosen independently of the external input. False and true give the same transition relation, establishing autonomy, but every state has only its singleton identity successor, so the family has no branch under any input.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Fibers/BranchingFreedomNeedsRelation.branching_freedom_strictly_stronger_than_autonomy`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/BranchingFreedomNeedsRelation.branching_process_is_not_functional`
- Truth anchor: `D5/S3/ConceptDynamics/Fibers/BranchingFreedomNeedsRelation.functional_process_is_not_branching`
