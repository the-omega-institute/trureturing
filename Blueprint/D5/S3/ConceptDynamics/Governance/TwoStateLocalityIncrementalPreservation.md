# Two-State Locality and Incremental Preservation

## Abstract

Two-state locality preserves a property outside a changed dependency set.

**Theorem 1.1 (Two-state locality yields incremental preservation).**

$$\begin{gathered}\forall State, Artifact, Value: \operatorname{Type},\\{}bytes: State \to \left(Artifact \to Value\right), reads: State \to \left(Artifact \to \operatorname{Set}\left(Artifact\right)\right),\\{}P: State \to \left(Artifact \to Prop\right), s, t: State, dep: Artifact \to \operatorname{Set}\left(Artifact\right),\\{}Local(bytes, reads, P) \Rightarrow {\forall x: Artifact, \operatorname{union}\left(reads(s, x), reads(t, x)\right) \subseteq dep(x)} \Rightarrow\\{}\forall x: Artifact, \neg x \in Changed(bytes, s, t) \Rightarrow \operatorname{Disjoint}\left(dep(x), Changed(bytes, s, t)\right) \Rightarrow\\{}(P(s, x) \Leftrightarrow P(t, x)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/TwoStateLocalityIncrementalPreservation.two_state_locality_yields_incremental_preservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Changed(bytes,s,t) is the set of artifacts whose bytes differ. Local quantifies over every pair of states and requires equality on x together with both states' actual read sets.

For the fixed states, dep over-approximates the union of both actual read sets at every artifact. Disjointness from Changed therefore makes every dependency used at x byte-equal.

The unchanged premise supplies byte equality at x itself. Those equalities discharge the locality antecedent and yield the stated equivalence; the equivalence is not an assumption.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/TwoStateLocalityIncrementalPreservation.two_state_locality_yields_incremental_preservation`
