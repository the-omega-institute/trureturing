# Global Profile Quotient Universality

## Abstract

The simultaneous-kernel quotient of a dependent family of readouts is the coarsest interface that recovers every component, with finite-subfamily recovery reduced to singleton tests and nonempty states shown necessary.

**Lemma 1.1 (Global profile equivalence is pointwise agreement).**

$$\begin{gathered}\forall P, X: \operatorname{Type},\\{}O: P \to \operatorname{Type}, q: (p: P) \to X \to O\left(p\right),\\{}\forall x, y: X,\\{}(x, y) \in \operatorname{globalProfileRelation}\left(q\right) \iff \forall p: P, q\left(p, x\right) = q\left(p, y\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality.global_profile_relation_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two states belong to the global profile relation exactly when every local readout gives them the same value. Equality of the dependent profiles yields each component equality, and the converse assembles those equalities into equality of the whole profile.

The output type may vary with the index. The statement therefore compares the two readout values separately inside the appropriate output type at each index.

**Lemma 1.2 (Every local readout factors through the global profile quotient).**

$$\begin{gathered}\forall P, X: \operatorname{Type},\\{}O: P \to \operatorname{Type}, q: (p: P) \to X \to O\left(p\right),\\{}\forall p: P, \operatorname{Refines}\left(q\left(p\right), \operatorname{globalProfileProjection}\left(q\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality.local_readouts_factor_through_global_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each index, the corresponding local readout is constant on the simultaneous-kernel classes. It therefore descends to a readout on the global profile quotient, and composing that descended readout with the canonical projection recovers the original component.

This recovery uses only the definition of the quotient relation. It needs neither an inhabited state space nor an inhabited index type.

**Theorem 1.3 (The global profile quotient is the universal recovering interface).**

$$\begin{gathered}\forall P, X: \operatorname{Type},\\{}O: P \to \operatorname{Type}, q: (p: P) \to X \to O\left(p\right),\\{}\operatorname{Nonempty}\left(X\right) \Rightarrow\\{}[(\forall p: P, \operatorname{Refines}\left(q\left(p\right), \operatorname{globalProfileProjection}\left(q\right)\right)) \land\\{}(\forall R: \operatorname{Type}, r: X \to R,\\{}(\forall p: P, \operatorname{Refines}\left(q\left(p\right), r\right)) \Rightarrow \operatorname{Refines}\left(\operatorname{globalProfileProjection}\left(q\right), r\right)) \land\\{}(\forall R: \operatorname{Type}, r: X \to R,\\{}\operatorname{RecoversFiniteSubfamilies}\left(q, r\right) \Rightarrow \operatorname{Refines}\left(\operatorname{globalProfileProjection}\left(q\right), r\right))].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality.global_profile_quotient_universality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The canonical quotient projection recovers every member of the dependent readout family. Conversely, if an interface recovers every local readout, states in one of its fibers have identical global profiles, so the quotient projection factors through that interface.

Thus the simultaneous-kernel quotient is coarsest among all interfaces that recover every component: any such interface retains enough information to determine the quotient class. Nonemptiness of the state space supplies a quotient value for interface points that are not represented by a state.

It also suffices to require recovery for every finite indexed subfamily. Applying that hypothesis to the singleton index type recovers an arbitrary chosen component, after which the same universal factorization applies.

**Lemma 1.4 (Empty states obstruct unrestricted factorization).**

$$\begin{gathered}q: (p: \emptyset) \to \emptyset \to Unit, r: \emptyset \to Unit,\\{}[(\forall p: \emptyset, \operatorname{Refines}\left(q\left(p\right), r\right)) \land\\{}\neg \operatorname{Refines}\left(\operatorname{globalProfileProjection}\left(q\right), r\right)].\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality.empty_state_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take both the state type and the readout index type to be empty. Recovery of every local readout through the unique map to Unit is then vacuous because there are no local components.

Nevertheless, the global quotient projection cannot factor through that map: such a factor would send the inhabited type Unit into the quotient of an empty state type, which has no element. This is the precise obstruction excluded by the main theorem's nonempty-state hypothesis.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality.empty_state_obstruction`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality.global_profile_quotient_universality`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality.global_profile_relation_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Sufficiency/GlobalProfileQuotientUniversality.local_readouts_factor_through_global_profile`
- Dependency: [D5/S3/ConceptDynamics/Sufficiency/MinimalPredictiveCompletionQuotient](MinimalPredictiveCompletionQuotient.md)
