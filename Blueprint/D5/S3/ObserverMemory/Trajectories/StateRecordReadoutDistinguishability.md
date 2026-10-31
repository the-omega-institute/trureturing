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

For a measurable history carrier and finite measurable state and record-output types with measurable singletons, assume that the endpoint and record-output maps are measurable, and put Dirac probability laws on two certified histories. If their endpoints agree, their endpoint pushforward laws are equal and their finite statistical TV is zero. If the two finite outputs q2(recordImage(history)) differ, the corresponding record-output laws are distinct Dirac laws, with statistical TV one. This law interpretation uses the same observe map and preserves observe_advance.

A generated example has Unit state, Boolean readings, List Bool records, append(r,b)=r++[b], the list-prefix relation, constant reading true, and controlledUpdate returning the Unit state. Take the initial history at ((),[]) and one next step with control false. The certified observations are ((),[]) and ((),[true]); the endpoints agree while the records differ. With q2=list.isEmpty their outputs are true and false, so their record-output TV is one. Replacing q2 by a constant gives TV zero despite the same distinct record images. This is a conditional discrimination statement, not a claim that distinct records always yield distinct outputs or that arbitrary history functions satisfy the certified evolution law.

The theorem does not claim that q2 separates every pair of distinct records. A constant q2 makes both sides of the equivalence false, as required by the source's conditional wording.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability.state_record_readout_distinguishability`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../../ConceptDynamics/ConceptFiberDecomposition.md)
