# RarePriorFullFields

## Abstract

RarePriorFullFields

The deterministic acquired row and complete renderer use the original partial native update. Counts and payload-return counters remain in the source. Finite fields retain every write, latch, held record and ordered event block. Factorization holds for every stream, including distinct infinite seed paths.

**Theorem 1.1 (deterministic actual rows).**

$$\forall ( \operatorname{ops} : \operatorname{List} \operatorname{Operation} ) , ( \forall ( \operatorname{c} : \operatorname{AcquiredNativeState} ) , ( ( \operatorname{run} \operatorname{ops} = \operatorname{some} \operatorname{c} ) \Rightarrow ( \exists \operatorname{z} : \operatorname{Runtime} , \operatorname{runtimeRun} \operatorname{ops} = \operatorname{some} \operatorname{z} \land \operatorname{z} . \operatorname{fields} = \operatorname{c} . \operatorname{source} . \operatorname{finiteFields} \land \operatorname{NativeObserverJointLaw} . \operatorname{row} \operatorname{actualObserver} \operatorname{ops} = \operatorname{PMF} . \operatorname{pure} \operatorname{z} \land ( \forall \operatorname{op} : \operatorname{Operation} , \operatorname{NativeObserverJointLaw} . \operatorname{row} \operatorname{actualObserver} ( \operatorname{ops} + + [ \operatorname{op} ] ) = \operatorname{actualUpdate} \operatorname{op} \operatorname{z} ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFullFields.deterministic_actual_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.2 (full fields factorization).**

$$\forall ( \operatorname{c} : \operatorname{AcquiredNativeState} ) , ( \forall ( \operatorname{omega} : \operatorname{Stream} ) , ( \operatorname{fullTranscript} \operatorname{c} \operatorname{omega} = \operatorname{fieldsTranscript} \operatorname{c} . \operatorname{source} . \operatorname{finiteFields} \operatorname{omega} \land ( \forall ( \operatorname{d} : \operatorname{AcquiredNativeState} ) , \operatorname{c} . \operatorname{source} . \operatorname{finiteFields} = \operatorname{d} . \operatorname{source} . \operatorname{finiteFields} \Rightarrow \operatorname{fullTranscript} \operatorname{c} \operatorname{omega} = \operatorname{fullTranscript} \operatorname{d} \operatorname{omega} ) \land ( \forall ( \operatorname{s} : \operatorname{ActivePhase} ) ( \operatorname{t} : \operatorname{ValidTail} \operatorname{s} ) , \operatorname{fullRenderer} \operatorname{c} \operatorname{s} \operatorname{t} = \operatorname{fieldsRenderer} \operatorname{c} . \operatorname{source} . \operatorname{finiteFields} \operatorname{s} \operatorname{t} ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFullFields.full_fields_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFullFields.deterministic_actual_rows`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFullFields.full_fields_factorization`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw](NativeObserverJointLaw.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode](RarePriorResidentCode.md)
