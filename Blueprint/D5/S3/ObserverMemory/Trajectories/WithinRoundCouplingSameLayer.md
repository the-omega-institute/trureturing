# Within-Round Coupling and Same-Layer Evaluation

## Abstract

The source coupling implication is retained, while the current same-layer encoding is explicitly recorded as unconditional.

**Theorem 1.1 (Coupling places both observers on one layer).**

$$\forall X, Lambda_{1}, A, Y_{2}: \operatorname{Type},\ R: \operatorname{AppendOnlyOps}\left(Lambda_{1}, A\right),\ q1: X \to A,\ controlledUpdate: RoundIndex \to \left(\operatorname{Prod}\left(X, Y_{2}\right) \to X\right),\ q2: Lambda_{1} \to Y_{2},\ e: RoundIndex,\ (\neg \operatorname{WithinRoundDecoupled}\left(controlledUpdate, e\right)) \Rightarrow\ (\operatorname{IsSameLayerInRound}\left(R, q1, controlledUpdate, q2, e\right)) \land\ (EstablishedClosureNonimplications).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer.within_round_coupling_is_same_layer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let e be a positive round index. The append-only operations R and the maps q1 : X -> A, controlledUpdate : RoundIndex -> X x Y2 -> X, and q2 : Lambda1 -> Y2 are exactly the data of the recorded observer at that round.

WithinRoundDecoupled says that controlledUpdate e has the same value for every pair of Y2 inputs at each state. The theorem assumes the negation of precisely that condition.

CrossRoundUpdateSchedule records the separate inter-round clause. The update at nextRound e is selected by a function receiving q2 of the preceding round's terminal record. IsSecondLayerObserver is the all-round predicate requiring WithinRoundDecoupled at every round.

The first public conjunct is IsSameLayerInRound. Its definition contains exactly the two clauses in Definition 45.2: jointRoundUpdate is pointwise the displayed Definition 45.1 update, and q2 evaluation on the joint quotient is the same-typed diagonal self-application. Failure of decoupling is not part of this conclusion predicate.

The current encoding proves IsSameLayerInRound for every round update, without using the coupling premise, because both clauses are definitional equalities. This fidelity boundary remains open. Re-entry requires a source-supported account of q2 evaluation as same-layer self-application that is not definitionally true for every update; no source-unsupported conjunct may be added.

The second conjunct is EstablishedClosureNonimplications, definitionally the proposition already proved by closure_nonimplication_triple for Sections 32.10 and 33.10. No universal surjectivity predicate or round-specific closure semantics is introduced here. The cited countermodels say only that the closures are not implied; they do not say that every enriched closure is impossible.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer.within_round_coupling_is_same_layer`
- Dependency: [D5/S3/Observer/Completion/ClosureNonimplicationTriple](../../Observer/Completion/ClosureNonimplicationTriple.md)
- Dependency: [D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability](StateRecordReadoutDistinguishability.md)
