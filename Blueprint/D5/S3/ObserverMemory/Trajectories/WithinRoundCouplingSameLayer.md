# Within-Round Coupling and Same-Layer Evaluation

## Abstract

A coupled recorded round is a same-layer augmented system, without an automatic self-description closure implication.

**Theorem 1.1 (Coupling places both observers on one layer).**

$$\forall X, Lambda_{1}, A, Y_{2}: \operatorname{Type},\ R: \operatorname{AppendOnlyOps}\left(Lambda_{1}, A\right),\ q1: X \to A,\ controlledUpdate: RoundIndex \to \left(\operatorname{Prod}\left(X, Y_{2}\right) \to X\right),\ q2: Lambda_{1} \to Y_{2},\ e: RoundIndex,\ (\neg \operatorname{WithinRoundDecoupled}\left(controlledUpdate, e\right)) \Rightarrow\ (\operatorname{IsSameLayerInRound}\left(R, q1, controlledUpdate, q2, e\right)) \land\ (\neg \operatorname{SameLayerSelfDescriptionClosureAutomatic}\left(X, Lambda_{1}, A, Y_{2}\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer.within_round_coupling_is_same_layer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let e be a positive round index. The append-only operations R and the maps q1 : X -> A, controlledUpdate : RoundIndex -> X x Y2 -> X, and q2 : Lambda1 -> Y2 are exactly the data of the recorded observer at that round.

WithinRoundDecoupled says that controlledUpdate e has the same value for every pair of Y2 inputs at each state. The theorem assumes the negation of precisely that condition.

The first public conjunct is IsSameLayerInRound. Its joint state is X x Lambda1, its update substitutes q2(lambda) into the controlled update, and its joint readout is (q1(x), q2(lambda)). On the kernel quotient of that readout, the canonical q2 evaluation is indexed twice by the same quotient and its diagonal is q2 itself.

The second public conjunct negates SameLayerSelfDescriptionClosureAutomatic. Expanded, it says that there is no universal rule taking every same-layer recorded round to surjectivity of its canonical q2 evaluation. This coupled round is the counterexample. Coupling supplies two distinct Y2 values; swapping one with the other and sending all remaining values to the first gives a fixed-point-free twist. The imported Lawvere diagonal theorem then supplies the missing table.

Thus the second conjunct is a non-implication statement. It does not claim that every enriched or higher-layer closure is impossible.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer.within_round_coupling_is_same_layer`
- Dependency: [D5/S0/Diagonal/Lawvere/QualitativeEscape](../../../S0/Diagonal/Lawvere/QualitativeEscape.md)
- Dependency: [D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability](StateRecordReadoutDistinguishability.md)
