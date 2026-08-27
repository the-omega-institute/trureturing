# Dynamic Profile Causal Closure

## Abstract

Every intervention descends to the complete control profile through the canonical right shift of action indices.

**Theorem 1.1 (The dynamic profile carries every intervention by right shift).**

$$\forall M \in \operatorname{Type}, X \in \operatorname{Type}, O \in \operatorname{Type},\; \left(\operatorname{Monoid}\left(M\right) \land \operatorname{MulAction}\left(M, X\right)\right) \Rightarrow \left(\forall q \in X \to O, u \in M,\; \operatorname{controlProfile}\left(q\right) \circ (x \mapsto u \cdot x) = (phi \mapsto (m \mapsto phi\left(m \cdot u\right))) \circ \operatorname{controlProfile}\left(q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Control/DynamicProfileCausalClosure.dynamic_profile_causal_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete profile is constructed from the public readout and the monoid action: its coordinate at an action records the readout after that action is applied to the state.

After a new intervention, evaluating the resulting profile at a continuation is therefore the old profile at the continuation multiplied on the right by that intervention. The displayed commuting equation exposes this macroscopic update directly.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Control/DynamicProfileCausalClosure.dynamic_profile_causal_closure`
- Dependency: [D5/S3/ConceptDynamics/Control/ControlQuotientUniversalMinimality](ControlQuotientUniversalMinimality.md)
