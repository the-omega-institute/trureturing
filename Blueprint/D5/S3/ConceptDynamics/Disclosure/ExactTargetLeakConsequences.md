# Consequences of Exact Target Leakage

## Abstract

Exact realization forces its sensitive part and obstructs zero new leakage.

**Theorem 1.1 (Exact realization forces and enlarges sensitive disclosure).**

$$\forall X \in \operatorname{Type}, P \in \operatorname{Type}, M \in \operatorname{Type}, S \in \operatorname{Type}, E \in \operatorname{Type}, K \in \operatorname{Type}, L \in \operatorname{Type}, p \in X \to P, m \in X \to M, s \in X \to S, e \in X \to E, k \in X \to K, l \in X \to L,\; \left(\operatorname{Refines}\left(e, \operatorname{conceptJoin}\left(p, m\right)\right) \land \left(\operatorname{IsConceptMeet}\left(e, s, k\right) \land \operatorname{IsConceptMeet}\left(\operatorname{conceptJoin}\left(p, m\right), s, l\right)\right)\right) \Rightarrow \left(\operatorname{Refines}\left(k, l\right) \land \left(\forall Before \in \operatorname{Type}, before \in X \to Before,\; \left(\neg \operatorname{Refines}\left(k, before\right)\right) \Rightarrow \left(\neg \operatorname{StructurallyNoNewLeak}\left(p, m, s, before, l\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Disclosure/ExactTargetLeakConsequences.exact_target_leak_consequences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target factors through the join of the public and added concepts. The forced part is explicitly the meet of target and sensitive, while the leak is the meet of the augmented public concept and the same sensitive concept.

The first conjunct is the forced-refinement theorem. The second states that structural no-new-leak is impossible whenever the forced part does not refine the named prior common part; the canonical predicate itself requires that prior readout to be the public-sensitive meet.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Disclosure/ExactTargetLeakConsequences.exact_target_leak_consequences`
- Dependency: [D5/S3/ConceptDynamics/Disclosure/ExecutionPrivacyObstruction](ExecutionPrivacyObstruction.md)
