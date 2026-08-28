# Typed Producer Resolution

## Abstract

Producer actors enter artifact dependency edges only through typed resolution; unresolved actors fail closed.

**Theorem 1.1 (Unresolved producer actors create no artifact edge and no admissible graph).**

$$\begin{gathered}\forall Artifact, ProducerActor: Type,\\{}producer: Artifact \to \operatorname{Option}\left(ProducerActor\right), resolve: ProducerActor \to \operatorname{Option}\left(Artifact\right), x: Artifact, q: ProducerActor,\\{}producer(x) = \operatorname{some}\left(q\right) \land resolve(q) = none \longrightarrow\\{}(\forall a: Artifact, \neg \operatorname{ProducerEdge}\left(producer, resolve, a, x\right)) \land \neg \operatorname{ResolutionComplete}\left(producer, resolve\right) \land\\{}\neg \exists E: Artifact \to Artifact \to Prop, \operatorname{AdmissibleProducerGraph}\left(producer, resolve, E\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Governance/TypedProducerResolution.typed_producer_resolution_fail_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Artifact and ProducerActor are independent types. The producer map returns an actor, while only the resolver can return an artifact endpoint for the artifact-to-artifact edge relation.

If producer(x) returns q but resolve(q) is none, every putative edge witness would require the contradictory equality resolve(q)=some(a). Hence no artifact edge enters x.

The same unresolved actor contradicts ResolutionComplete. Because an AdmissibleProducerGraph contains resolution completeness together with exact agreement with ProducerEdge, no such graph exists.

This is a fail-closed result: the actor is not silently accepted as an empty producer family merely because it contributes no edge.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Governance/TypedProducerResolution.typed_producer_resolution_fail_closed`
