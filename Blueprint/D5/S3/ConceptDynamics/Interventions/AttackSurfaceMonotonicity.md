# Attack Surface Monotonicity

## Abstract

Permission expansion enlarges reachable states, preserves bad-state inclusion, and can enlarge both permissions and reachability strictly.

**Theorem 1.1 (Permission expansion enlarges reachability).**

$$\forall State \in \operatorname{Type}, Permission \in \operatorname{Type}, step \in Permission \to \left(State \to \left(State \to Prop\right)\right), P \in \operatorname{Set}\left(Permission\right), Q \in \operatorname{Set}\left(Permission\right), start \in State,\; P \subseteq Q \Rightarrow \operatorname{Reach}\left(step, P, start\right) \subseteq \operatorname{Reach}\left(step, Q, start\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/AttackSurfaceMonotonicity.reach_monotone_in_permissions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a permission-indexed transition relation, the reachable set from a fixed start state contains every state connected by a finite chain whose permissions all lie in the allowed set.

If one permission set is contained in another, every transition admitted by the smaller set remains admitted by the larger set. The same finite chains therefore witness inclusion of the two reachable sets.

This is covariance of attack surface with permission: adding allowed actions cannot remove a state that was already reachable.

**Lemma 1.2 (Bad-state reachability remains monotone).**

$$\forall State \in \operatorname{Type}, Permission \in \operatorname{Type}, step \in Permission \to \left(State \to \left(State \to Prop\right)\right), P \in \operatorname{Set}\left(Permission\right), Q \in \operatorname{Set}\left(Permission\right), start \in State, bad \in \operatorname{Set}\left(State\right),\; P \subseteq Q \Rightarrow \operatorname{intersection}\left(\operatorname{Reach}\left(step, P, start\right), bad\right) \subseteq \operatorname{intersection}\left(\operatorname{Reach}\left(step, Q, start\right), bad\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/AttackSurfaceMonotonicity.bad_state_reach_monotone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix any collection of bad states. Expanding the allowed permissions preserves every previously reachable bad state, so intersecting both attack surfaces with that collection preserves inclusion.

The bad-state predicate contributes no additional transition behavior; it simply filters the two reachable sets by the same criterion.

**Lemma 1.3 (Boolean negation witnesses strict growth).**

$$\exists P \in \operatorname{Set}\left(Bool \to Bool\right), Q \in \operatorname{Set}\left(Bool \to Bool\right),\; P \subset Q \land \operatorname{Reach}\left((permission, source, target) \mapsto permission\left(source\right) = target, P, false\right) \subset \operatorname{Reach}\left((permission, source, target) \mapsto permission\left(source\right) = target, Q, false\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Interventions/AttackSurfaceMonotonicity.strict_growth_witness` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Use Boolean functions as permissions and let a permitted function move a source state to its value. Starting from false, the empty permission set reaches only false, while the singleton permission set containing negation also reaches true.

Thus the empty set is a proper subset of the negation permission set, and its reachable set is a proper subset of the enlarged reachable set. Permission growth and attack-surface growth can therefore both be strict.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Interventions/AttackSurfaceMonotonicity.bad_state_reach_monotone`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/AttackSurfaceMonotonicity.reach_monotone_in_permissions`
- Truth anchor: `D5/S3/ConceptDynamics/Interventions/AttackSurfaceMonotonicity.strict_growth_witness`
