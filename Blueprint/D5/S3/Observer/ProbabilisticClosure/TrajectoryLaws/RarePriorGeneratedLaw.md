# RarePriorGeneratedLaw

## Abstract

RarePriorGeneratedLaw

The decoder accepts only Runtime and the fixed installed service semantics. A marked trajectory records the same deterministic runtime update and selected threshold. Complete infinite-path restart, event-block deletion, and terminal branches establish the configuration residual law. Original history conditioning uses the published source/private product law and a deterministic actual row. No interpreter budget or broad COMPLETE membership is asserted here.

**Theorem 1.1 (terminal path invariance).**

$$\forall ( \operatorname{z} : \operatorname{Runtime} ) , ( ( \exists \operatorname{b} , \operatorname{z} . \operatorname{fields} . \operatorname{control} = . \operatorname{fourth} ( . \operatorname{pending} \operatorname{b} ) ) \lor \operatorname{z} . \operatorname{fields} . \operatorname{control} = . \operatorname{fourth} . \operatorname{delivered} ) \Rightarrow \forall ( \operatorname{p} \operatorname{q} : \operatorname{Nat} \Rightarrow \operatorname{Marked} ) , \operatorname{renderPath} \operatorname{z} \operatorname{p} = \operatorname{renderPath} \operatorname{z} \operatorname{q}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.terminal_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.2 (terminal Dirac law).**

$$\forall ( \operatorname{z} : \operatorname{Runtime} ) , ( ( \exists \operatorname{b} , \operatorname{z} . \operatorname{fields} . \operatorname{control} = . \operatorname{fourth} ( . \operatorname{pending} \operatorname{b} ) ) \lor \operatorname{z} . \operatorname{fields} . \operatorname{control} = . \operatorname{fourth} . \operatorname{delivered} ) \Rightarrow \operatorname{decoder} \operatorname{z} = \operatorname{Measure} . \operatorname{dirac} ( \operatorname{renderPath} \operatorname{z} ( \operatorname{fun} _ \mapsto ( \operatorname{z} , 0 ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.terminal_dirac` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.3 (fields measurable).**

$$\forall ( \operatorname{f} : \operatorname{FiniteFields} ) , ( \operatorname{Measurable} ( \operatorname{fieldsTranscript} \operatorname{f} ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.fields_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.4 (conditioned read path).**

$$\forall ( \operatorname{z} : \operatorname{Runtime} ) , ( \forall ( \operatorname{x} : \operatorname{Letter} ) , ( ( \operatorname{ProbabilityTheory} . \operatorname{cond} ( \operatorname{pathLaw} \operatorname{z} ) \{ \operatorname{p} | \operatorname{p} 0 = ( \operatorname{z} , \operatorname{x} ) \} ) . \operatorname{map} ( \operatorname{fun} \operatorname{p} \operatorname{n} \mapsto \operatorname{p} ( \operatorname{n} + 1 ) ) = \operatorname{pathLaw} ( \operatorname{readAdvance} \operatorname{z} \operatorname{x} ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.conditioned_read_path` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.5 (first measurable).**

$$\operatorname{Measurable} \operatorname{firstOperation}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.first_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.6 (generated read compatibility).**

$$\forall ( \operatorname{z} : \operatorname{Runtime} ) , ( ( \forall \operatorname{x} , \operatorname{finiteOperation} \operatorname{z} . \operatorname{fields} \operatorname{x} = \operatorname{some} ( . \operatorname{read} \operatorname{x} ) ) \Rightarrow ( ( \forall \operatorname{x} , \exists \operatorname{d} , \operatorname{runtimeStep} \operatorname{z} ( . \operatorname{read} \operatorname{x} ) = \operatorname{some} \operatorname{d} ) \Rightarrow ( \forall ( \operatorname{x} : \operatorname{Letter} ) , ( ( \operatorname{decoder} \operatorname{z} ) \{ \operatorname{t} | \operatorname{firstOperation} \operatorname{t} = \operatorname{some} ( . \operatorname{read} \operatorname{x} ) \} = ( \operatorname{bernoulliMeasure} ( 0 : \operatorname{Letter} ) 1 ( \operatorname{emissionParameter} \operatorname{z} ) ) \{ \operatorname{x} \} \land ( \operatorname{ProbabilityTheory} . \operatorname{cond} ( \operatorname{decoder} \operatorname{z} ) \{ \operatorname{t} | \operatorname{firstOperation} \operatorname{t} = \operatorname{some} ( . \operatorname{read} \operatorname{x} ) \} ) . \operatorname{map} \operatorname{deleteBlock} = \operatorname{decoder} ( \operatorname{readAdvance} \operatorname{z} \operatorname{x} ) ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.generated_read_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.7 (configuration compatibility).**

$$\forall ( \operatorname{z} : \operatorname{Runtime} ) , ( ( ( \forall \operatorname{b} , \operatorname{z} . \operatorname{fields} . \operatorname{control} \neq . \operatorname{fourth} ( . \operatorname{pending} \operatorname{b} ) ) \Rightarrow \operatorname{z} . \operatorname{fields} . \operatorname{control} \neq . \operatorname{fourth} . \operatorname{delivered} \Rightarrow \forall \operatorname{x} : \operatorname{Letter} , ( \operatorname{decoder} \operatorname{z} ) \{ \operatorname{t} | \operatorname{firstOperation} \operatorname{t} = \operatorname{some} ( . \operatorname{read} \operatorname{x} ) \} = ( \operatorname{bernoulliMeasure} ( 0 : \operatorname{Letter} ) 1 ( \operatorname{emissionParameter} \operatorname{z} ) ) \{ \operatorname{x} \} \land ( \operatorname{ProbabilityTheory} . \operatorname{cond} ( \operatorname{decoder} \operatorname{z} ) \{ \operatorname{t} | \operatorname{firstOperation} \operatorname{t} = \operatorname{some} ( . \operatorname{read} \operatorname{x} ) \} ) . \operatorname{map} \operatorname{deleteBlock} = \operatorname{decoder} ( \operatorname{readAdvance} \operatorname{z} \operatorname{x} ) ) \land ( \forall \operatorname{b} : \operatorname{Letter} , \operatorname{z} . \operatorname{fields} . \operatorname{control} = . \operatorname{fourth} ( . \operatorname{pending} \operatorname{b} ) \Rightarrow ( \operatorname{decoder} \operatorname{z} ) \{ \operatorname{t} | \operatorname{firstOperation} \operatorname{t} = \operatorname{some} ( . \operatorname{stop} \operatorname{b} ) \} = 1 \land ( \operatorname{ProbabilityTheory} . \operatorname{cond} ( \operatorname{decoder} \operatorname{z} ) \{ \operatorname{t} | \operatorname{firstOperation} \operatorname{t} = \operatorname{some} ( . \operatorname{stop} \operatorname{b} ) \} ) . \operatorname{map} \operatorname{deleteBlock} = \operatorname{decoder} ( ( \operatorname{runtimeStep} \operatorname{z} ( . \operatorname{stop} \operatorname{b} ) ) . \operatorname{getD} \operatorname{z} ) ) \land ( \operatorname{z} . \operatorname{fields} . \operatorname{control} = . \operatorname{fourth} . \operatorname{delivered} \Rightarrow \operatorname{decoder} \operatorname{z} = \operatorname{Measure} . \operatorname{dirac} ( \operatorname{renderPath} \operatorname{z} ( \operatorname{fun} \operatorname{anonymous}_{\operatorname{anonymous}} \mapsto ( \operatorname{z} , 0 ) ) ) \land ( \operatorname{decoder} \operatorname{z} ) \{ \operatorname{t} | \operatorname{firstOperation} \operatorname{t} = \operatorname{none} \} = 1 \land \forall ( \operatorname{p} : \operatorname{Nat} \Rightarrow \operatorname{Marked} ) ( \operatorname{n} : \operatorname{Nat} ) , \operatorname{renderPath} \operatorname{z} \operatorname{p} ( \operatorname{n} + 1 ) = \operatorname{none} ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.configuration_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.8 (generated full law).**

$$\forall ( \operatorname{z} : \operatorname{Runtime} ) , ( \operatorname{IsProbabilityMeasure} ( \operatorname{decoder} \operatorname{z} ) \land 0 < ( \operatorname{emissionParameter} \operatorname{z} : \operatorname{Real} ) \land ( \operatorname{emissionParameter} \operatorname{z} : \operatorname{Real} ) < 1 \land \operatorname{returnedAlphaMass} ( \operatorname{selectedThreshold} \operatorname{z} ) = ( \operatorname{emissionParameter} \operatorname{z} : \operatorname{Real} ) \land ( \forall ( \operatorname{n} : \operatorname{Nat} ) ( \operatorname{w} : \operatorname{Fin} ( \operatorname{n} + 1 ) \Rightarrow \operatorname{Marked} ) , ( ( \operatorname{pathLaw} \operatorname{z} ) . \operatorname{map} \operatorname{fun} \operatorname{p} ( \operatorname{i} : \operatorname{Fin} ( \operatorname{n} + 1 ) ) \mapsto \operatorname{p} \operatorname{i} . \operatorname{val} ) \{ \operatorname{w} \} = \operatorname{markedInitial} \operatorname{z} \{ \operatorname{w} 0 \} * \operatorname{product} \operatorname{i} : \operatorname{Fin} \operatorname{n} , \operatorname{markedKernel} ( \operatorname{w} \operatorname{i} . \operatorname{castSucc} ) \{ \operatorname{w} \operatorname{i} . \operatorname{succ} \} ) \land ( \forall ( \operatorname{p} : \operatorname{Nat} \Rightarrow \operatorname{Marked} ) , ( \operatorname{p} 0 ) . 1 = \operatorname{z} \Rightarrow ( \forall \operatorname{n} , ( \operatorname{p} ( \operatorname{n} + 1 ) ) . 1 = \operatorname{readAdvance} ( \operatorname{p} \operatorname{n} ) . 1 ( \operatorname{p} \operatorname{n} ) . 2 ) \Rightarrow ( \forall \operatorname{n} , ( \operatorname{p} \operatorname{n} ) . 1 = \operatorname{readFold} \operatorname{z} ( \operatorname{fun} \operatorname{k} \mapsto ( \operatorname{p} \operatorname{k} ) . 2 ) \operatorname{n} ) \land \forall \operatorname{c} : \operatorname{AcquiredNativeState} , \operatorname{c} . \operatorname{source} . \operatorname{finiteFields} = \operatorname{z} . \operatorname{fields} \Rightarrow \operatorname{renderPath} \operatorname{z} \operatorname{p} = \operatorname{fullTranscript} \operatorname{c} ( \operatorname{fun} \operatorname{k} \mapsto ( \operatorname{p} \operatorname{k} ) . 2 ) ) \land ( \operatorname{AE} \operatorname{p} \operatorname{law} \operatorname{pathLaw} \operatorname{z} , ( \operatorname{p} 0 ) . 1 = \operatorname{z} \land \forall \operatorname{n} , ( \operatorname{p} ( \operatorname{n} + 1 ) ) . 1 = \operatorname{readAdvance} ( \operatorname{p} \operatorname{n} ) . 1 ( \operatorname{p} \operatorname{n} ) . 2 ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.generated_full_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

**Theorem 1.9 (history marginal compatibility).**

$$\forall ( \operatorname{mu} : \operatorname{PMF} \operatorname{NativeConditionalControl} . \operatorname{DepthLaw} . \operatorname{Depth} ) , ( \forall ( \operatorname{h} : \operatorname{List} \operatorname{Operation} ) , ( \forall ( \operatorname{c} : \operatorname{AcquiredNativeState} ) , ( \forall ( \operatorname{hc} : \operatorname{run} \operatorname{h} = \operatorname{some} \operatorname{c} ) , ( ( \operatorname{ProbabilityTheory} . \operatorname{cond} ( \operatorname{NativeObserverJointLaw} . \operatorname{actualLaw} \operatorname{actualObserver} \operatorname{mu} \operatorname{h} . \operatorname{length} ) ( \operatorname{NativeConditionalControl} . \operatorname{DepthLaw} . \operatorname{nativeEvent} \operatorname{h} \operatorname{c} \operatorname{setProduct} \operatorname{Set} . \operatorname{univ} ) ) . \operatorname{map} ( \operatorname{Prod} . \operatorname{map} ( \operatorname{fun} \operatorname{t} : \operatorname{NativeConditionalControl} . \operatorname{DepthLaw} . \operatorname{Depth} \times \operatorname{Stream} \mapsto ( \operatorname{t} . 1 , \operatorname{rawTail} \operatorname{t} . 2 ( \operatorname{readLetters} \operatorname{h} ) . \operatorname{length} ) ) \operatorname{id} ) = ( \operatorname{NativeConditionalControl} . \operatorname{DepthLaw} . \operatorname{jointLaw} ( \operatorname{NativeConditionalControl} . \operatorname{DepthLaw} . \operatorname{posterior} \operatorname{mu} \operatorname{h} \operatorname{c} \operatorname{hc} ) ) . \operatorname{prod} ( \operatorname{NativeObserverJointLaw} . \operatorname{row} \operatorname{actualObserver} \operatorname{h} ) . \operatorname{toMeasure} \land \exists \operatorname{z} : \operatorname{Runtime} , \operatorname{runtimeRun} \operatorname{h} = \operatorname{some} \operatorname{z} \land \operatorname{z} . \operatorname{fields} = \operatorname{c} . \operatorname{source} . \operatorname{finiteFields} \land \operatorname{NativeObserverJointLaw} . \operatorname{row} \operatorname{actualObserver} \operatorname{h} = \operatorname{PMF} . \operatorname{pure} \operatorname{z} \land \operatorname{historyGenerated} \operatorname{h} = \operatorname{decoder} \operatorname{z} \land \forall ( \operatorname{op} : \operatorname{Operation} ) ( \operatorname{d} : \operatorname{AcquiredNativeState} ) , \operatorname{nativeStep} \operatorname{c} \operatorname{op} = \operatorname{some} \operatorname{d} \Rightarrow \operatorname{NativeObserverJointLaw} . \operatorname{row} \operatorname{actualObserver} ( \operatorname{h} + + [ \operatorname{op} ] ) = \operatorname{actualUpdate} \operatorname{op} \operatorname{z} \land ( \operatorname{ProbabilityTheory} . \operatorname{cond} ( \operatorname{historyGenerated} \operatorname{h} ) \{ \operatorname{t} | \operatorname{firstOperation} \operatorname{t} = \operatorname{some} \operatorname{op} \} ) . \operatorname{map} \operatorname{deleteBlock} = \operatorname{historyGenerated} ( \operatorname{h} + + [ \operatorname{op} ] ) ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.history_marginal_compatibility` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The statement retains the complete original telescope and conditions.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.conditioned_read_path`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.configuration_compatibility`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.fields_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.first_measurable`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.generated_full_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.generated_read_compatibility`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.history_marginal_compatibility`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.terminal_constant`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorGeneratedLaw.terminal_dirac`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFullFields](RarePriorFullFields.md)
