# State and Record Readout Distinguishability

## Abstract

Append-generated records preserve endpoint collapse and conditional record separation.

**Theorem 1.1 (State readouts merge; record readouts separate conditionally).**

$$\forall X, A, Y, Y_{2}: \operatorname{Type},\ O: \operatorname{RecordedObserver}\left(X, A, Y_{2}\right),\ gamma, gammaPrime: \operatorname{ObserverHistory}\left(X, A, Y_{2}\right), x: X, lambda, lambdaPrime: \operatorname{AppendOnlyRecord}\left(A\right),\ (\operatorname{endpoint}\left(O\right)\left(gamma\right) = x \land \operatorname{endpoint}\left(O\right)\left(gammaPrime\right) = x \land \operatorname{recordImage}\left(O\right)\left(gamma\right) = lambda \land \operatorname{recordImage}\left(O\right)\left(gammaPrime\right) = lambdaPrime \land lambda \neq lambdaPrime) \Rightarrow\ (\forall s: X \to Y, s\left(\operatorname{endpoint}\left(O\right)\left(gamma\right)\right) = s\left(\operatorname{endpoint}\left(O\right)\left(gammaPrime\right)\right)) \land\ (\neg \operatorname{ker}\left(\operatorname{q2}\left(O\right) \circ \operatorname{recordImage}\left(O\right), gamma, gammaPrime\right) \iff \operatorname{q2}\left(O\right)\left(lambda\right) \neq \operatorname{q2}\left(O\right)\left(lambdaPrime\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability.state_record_readout_distinguishability` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let O be a RecordedObserver on a state type X, reading type A, and second-layer output Y2. Its fields are q1 : X -> A, the controlled update T1 : X x Y2 -> X, and q2 : AppendOnlyRecord A -> Y2. AppendOnlyRecord A stores a list; the operational transition changes it by lambda.append(q1(x)), so old entries remain a prefix.

An ObserverHistory contains an initial augmented state (x, lambda) and a finite list of second-layer inputs. Its endpoint and recordImage are the two projections obtained by folding the source one-step evolution over those inputs, so recordImage is not an arbitrary map.

Let two such generated histories have the same endpoint x and respective record images lambda and lambdaPrime, with the images distinct.

The first public conjunct quantifies over every state-only readout s. Since both histories end at x, their state readout values are equal.

The second public conjunct is an equivalence. The composed history readout q2 after the record-image map lies outside its equality kernel exactly when q2(lambda) and q2(lambdaPrime) differ. Thus its two directions are the source's two record-separation assertions.

The theorem does not claim that q2 separates every pair of distinct records. A constant q2 makes both sides of the equivalence false, as required by the source's conditional wording.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability.state_record_readout_distinguishability`
- Dependency: [D5/S3/ConceptDynamics/ConceptFiberDecomposition](../../ConceptDynamics/ConceptFiberDecomposition.md)
