# Within-Round Coupling and Same-Layer Evaluation

## Abstract

Definition 45.2 has an explicit augmented-system interface; Proposition 45.3 remains open at its independent Delta condition.

**Definition 1.1 (Same-layer data for an augmented recorded system).**

Lean statement: `D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer.IsSameLayerInRound`

*Formalization.* `D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer.IsSameLayerInRound` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Let e be a positive round index. The append-only operations R and the maps q1 : X -> A, controlledUpdate : RoundIndex -> X x Y2 -> X, and q2 : Lambda1 -> Y2 are exactly the data of the recorded observer at that round.

WithinRoundDecoupled says that controlledUpdate e has the same value for every pair of Y2 inputs at each state. Proposition 45.3 assumes the negation of precisely that condition.

CrossRoundUpdateSchedule records the separate inter-round clause. The update at nextRound e is selected by a function receiving q2 of the preceding round's terminal record. IsSecondLayerObserver is the all-round predicate requiring WithinRoundDecoupled at every round.

AugmentedSingleSystem gives dynamics, readout, and deltaEvaluation as separate fields. At Definition 45.2 the carrier is typed as X x Lambda1, the readout codomain as A x Y2, and the quotient as the kernel quotient of jointReadout. No constructor derives deltaEvaluation from q2.

IsSameLayerInRound requires three independent facts: the supplied readout equals jointReadout, the supplied dynamics equals Definition 45.1's closed-loop jointRoundUpdate, and the supplied Delta/evaluation diagonal agrees with q2 descended to the joint quotient.

Proposition 45.3 is intentionally not declared as proved. The coupling premise constrains controlledUpdate but supplies no relation for the independently given deltaEvaluation; coupling_does_not_force_delta_diagonal formalizes this obstruction. Re-entry requires source support deriving the already-given Delta diagonal law from coupling, or an independently specified Delta construction carrying that law. Defining Delta from q2 solely to make the equality reflexive is not a valid re-entry.

EstablishedClosureNonimplications remains the exact proposition already proved by closure_nonimplication_triple for Sections 32.10 and 33.10. That theorem does not provide the missing Delta relation.

## References

- Truth anchor: `D5/S3/ObserverMemory/Trajectories/WithinRoundCouplingSameLayer.IsSameLayerInRound`
- Dependency: [D5/S3/Observer/Completion/ClosureNonimplicationTriple](../../Observer/Completion/ClosureNonimplicationTriple.md)
- Dependency: [D5/S3/ObserverMemory/Trajectories/StateRecordReadoutDistinguishability](StateRecordReadoutDistinguishability.md)
