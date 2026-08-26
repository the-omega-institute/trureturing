# Exact Target Forced Leak

## Abstract

Exact target realization exposes its sensitive common part through the leak of the augmented public concept, and a no-new-leak hypothesis makes that exposure already present before augmentation.

**Theorem 1.1 (Exact target realization forces sensitive disclosure).**

$$\forall X \in \operatorname{Type}, P \in \operatorname{Type}, M \in \operatorname{Type}, S \in \operatorname{Type}, E \in \operatorname{Type}, K \in \operatorname{Type}, L \in \operatorname{Type}, p \in X \to P, m \in X \to M, s \in X \to S, e \in X \to E, k \in X \to K, l \in X \to L,\; \left(\operatorname{Refines}\left(e, \operatorname{conceptJoin}\left(p, m\right)\right) \land \left(\operatorname{IsConceptMeet}\left(e, s, k\right) \land \operatorname{IsConceptMeet}\left(\operatorname{conceptJoin}\left(p, m\right), s, l\right)\right)\right) \Rightarrow \operatorname{Refines}\left(k, l\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak.exact_target_forced_leak` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The target factors through the join of the public and added readouts. Because the forced part is the target's common part with the sensitive readout, transitivity also makes it factor through that augmented public join.

The forced part already factors through the sensitive readout. These two lower-bound factorizations invoke the universal property of the augmented join's meet with the sensitive readout, forcing the part to factor through the resulting leak.

**Lemma 1.2 (Structural no-new-leak makes the forced leak preexist).**

$$\forall X \in \operatorname{Type}, P \in \operatorname{Type}, M \in \operatorname{Type}, S \in \operatorname{Type}, E \in \operatorname{Type}, K \in \operatorname{Type}, Before \in \operatorname{Type}, After \in \operatorname{Type}, p \in X \to P, m \in X \to M, s \in X \to S, e \in X \to E, k \in X \to K, before \in X \to Before, after \in X \to After,\; \left(\operatorname{Refines}\left(e, \operatorname{conceptJoin}\left(p, m\right)\right) \land \left(\operatorname{IsConceptMeet}\left(e, s, k\right) \land \operatorname{StructurallyNoNewLeak}\left(p, m, s, before, after\right)\right)\right) \Rightarrow \operatorname{Refines}\left(k, before\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak.forced_leak_preexists_of_structurally_no_new_leak` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The main theorem first places the target-forced sensitive part below the post-augmentation common part. Structural no-new-leak identifies that post-augmentation part with the prior public-sensitive common part in both refinement directions. Composing the relevant direction shows that the forced part was already disclosed by the public readout.

**Lemma 1.3 (Boolean coordinates give a nontrivial witness).**

$$\operatorname{Refines}\left(snd, \operatorname{conceptJoin}\left(fst, snd\right)\right) \land \left(\operatorname{IsConceptMeet}\left(snd, snd, snd\right) \land \left(\operatorname{IsConceptMeet}\left(\operatorname{conceptJoin}\left(fst, snd\right), snd, snd\right) \land \left(\operatorname{Refines}\left(snd, snd\right) \land \left(\exists x \in Bool \times Bool, y \in Bool \times Bool,\; snd\left(x\right) \ne snd\left(y\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak.exact_target_forced_leak_nontrivial_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On pairs of Booleans, take the public readout to be the first coordinate and the added, sensitive, target, forced-part, and leak readouts to be the second coordinate. The product join realizes the target, and the second coordinate satisfies both meet conditions. The states (false, false) and (false, true) receive different forced-part values, so the instance carries genuine disclosure rather than a constant readout.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak.exact_target_forced_leak`
- Truth anchor: `D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak.exact_target_forced_leak_nontrivial_witness`
- Truth anchor: `D5/S3/ConceptDynamics/Disclosure/ExactTargetForcedLeak.forced_leak_preexists_of_structurally_no_new_leak`
- Dependency: [D5/S3/ConceptDynamics/Interventions/RedundantAppealDefectPersistence](../Interventions/RedundantAppealDefectPersistence.md)
- Dependency: [D5/S3/ConceptDynamics/Refinement/RefinementTransitivity](../Refinement/RefinementTransitivity.md)
