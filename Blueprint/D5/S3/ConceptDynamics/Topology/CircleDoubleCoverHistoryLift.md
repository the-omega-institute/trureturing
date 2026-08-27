# History Lifts in the Circle Double Cover

## Abstract

The circle double cover has canonical history-dependent path lifts.

**Theorem 1.1 (Initial upper data and path history determine the lifted branch).**

$$\begin{aligned}let p: Circle \to Circle, p(z) = z^{2};\\{}let cov = \operatorname{isCoveringMap}(\operatorname{CircleNpowQuotientCover}(2));\\{}(\forall \Gamma: \operatorname{ContinuousMap}(I, Circle), e: Circle, \Gamma(0) = p(e), let \widetilde{\Gamma} = \operatorname{liftPath}(cov, \Gamma, e, \Gamma(0) = p(e)); p \circ \widetilde{\Gamma} = \Gamma \land \widetilde{\Gamma}(0) = e \land \forall \gamma: \operatorname{ContinuousMap}(I, Circle), p \circ \gamma = \Gamma \land \gamma(0) = e \Rightarrow \gamma = \widetilde{\Gamma}) \land\\{}(\neg \exists s: Circle \to Circle, \operatorname{Continuous}(s) \land \forall z: Circle, p(s(z)) = z) \land\\{}let \omega: \operatorname{ContinuousMap}(I, Circle), \forall t: I, \omega(t) = \operatorname{CircleExp}(2 \pi t);\\{}let \widetilde{\omega} = \operatorname{liftPath}(cov, \omega, 1, \omega(0) = p(1));\\{}p \circ \widetilde{\omega} = \omega \land \widetilde{\omega}(0) = 1 \land \widetilde{\omega}(1) = -1.\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverHistoryLift.circle_double_cover_history_lift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The public object is Mathlib's canonical liftPath for the squaring covering map. Its lift equation, initial-value computation, and uniqueness characterization are all stated directly.

A continuous state-only selector would be a global section of the squaring map, which the imported no-section theorem excludes. The path lift remains available because it also receives the initial upper point and the complete base path.

For the explicit once-around loop based at one, the canonical lift is the half-angle path. It starts at one and ends at minus one, exhibiting the exchange of the two points over the basepoint.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Topology/CircleDoubleCoverHistoryLift.circle_double_cover_history_lift`
- Dependency: [D5/S3/ConceptDynamics/Topology/CircleDoubleCoverNoSection](CircleDoubleCoverNoSection.md)
