# State and Record Readout Distinguishability

## Abstract

Abstract histories preserve endpoint collapse and conditional record separation.

**Theorem 1.1 (State readouts merge; record readouts separate conditionally).**

$$\forall X, Lambda_{1}, A, Y, Y_{2}, H: \operatorname{Type},\ R: \operatorname{AppendOnlyOps}\left(Lambda_{1}, A\right),\ O: \operatorname{RecordedObserver}\left(X, Lambda_{1}, A, Y_{2}, R\right),\ E: \operatorname{HistoryEvolution}\left(H, X, Lambda_{1}, A, Y_{2}, R, O\right),\ gamma, gammaPrime: H, x: X, lambda, lambdaPrime: Lambda_{1},\ (\operatorname{endpoint}\left(E\right)\left(gamma\right) = x \land \operatorname{endpoint}\left(E\right)\left(gammaPrime\right) = x \land \operatorname{recordImage}\left(E\right)\left(gamma\right) = lambda \land \operatorname{recordImage}\left(E\right)\left(gammaPrime\right) = lambdaPrime \land lambda \neq lambdaPrime) \Rightarrow\ (\forall s: X \to Y, s\left(\operatorname{endpoint}\left(E\right)\left(gamma\right)\right) = s\left(\operatorname{endpoint}\left(E\right)\left(gammaPrime\right)\right)) \land\ (\neg \operatorname{ker}\left(\operatorname{q2}\left(O\right) \circ \operatorname{recordImage}\left(E\right), gamma, gammaPrime\right) \iff \operatorname{q2}\left(O\right)\left(lambda\right) \neq \operatorname{q2}\left(O\right)\left(lambdaPrime\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability.state_record_readout_distinguishability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Lambda1 be a record type equipped with named AppendOnlyOps: append, a monotonic prefix relation, and a certificate that append preserves that relation. Let O be a RecordedObserver with q1 : X -> A, the controlled update T1 : X x Y2 -> X, and q2 : Lambda1 -> Y2.

Let H be an abstract history carrier. A HistoryEvolution E supplies an advance operation and an observation H -> X x Lambda1, with a law identifying the observation after advance with the source one-step evolution. Endpoint and recordImage are the two projections of that single certified observation.

Let two histories in H have the same endpoint x and respective record images lambda and lambdaPrime, with the images distinct.

The first public conjunct quantifies over every state-only readout s. Since both histories end at x, their state readout values are equal.

The second public conjunct is an equivalence. The composed history readout q2 after the record-image map lies outside its equality kernel exactly when q2(lambda) and q2(lambdaPrime) differ. Thus its two directions are the source's two record-separation assertions.

The theorem does not claim that q2 separates every pair of distinct records. A constant q2 makes both sides of the equivalence false, as required by the source's conditional wording.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability.state_record_readout_distinguishability`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../../ConceptDynamics/ConceptFiberDecomposition.md)
