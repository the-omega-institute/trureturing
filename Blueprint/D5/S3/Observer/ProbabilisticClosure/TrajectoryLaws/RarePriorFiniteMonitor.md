# RarePriorFiniteMonitor

## Abstract

RarePriorFiniteMonitor

The monitor begins with the first paid Read. Its only count register is Fin 376 with saturation at 375. The block is six alpha bits followed by ten beta bits; the suffix is beta alpha, beta beta alpha alpha. An independent prefix grammar establishes exact whole-word recognition. The finite block position, suffix position, accepted state and sink hold no history.

Runtime is the original FiniteFields together with the monitor and one-shot mode. Every transaction first calls the original partial finiteStep. The legal-history projection keeps original Counts and payloadReturns in the source rather than in the observer. Third-write activation follows the original marker writer and bare snapshot latch.

G alpha completes; G beta enters Gbeta. Gbeta beta completes; Gbeta alpha executes the original return and disables special operation permanently. Seeds, early phases and other legal histories use the ordinary query row. Pending permits only matching Stop, and delivered permits neither Read nor Stop. Off-permission matrix rows grant no terminal Read.

**Theorem 1.1 (whole word recognition).**

$$\forall ( \operatorname{w} : \operatorname{List} \operatorname{Letter} ) , ( \operatorname{scanWord} \operatorname{monitorInitial} \operatorname{w} = . \operatorname{accepted} \Leftrightarrow \exists \operatorname{n} : \mathbb{N} , 375 \leq \operatorname{n} \land \operatorname{w} = \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.whole_word_recognition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The prefix invariant distinguishes complete blocks, incomplete blocks, suffix positions and the sink. Acceptance is equivalent to a complete word with at least 375 blocks.

**Theorem 1.2 (runtime projection).**

$$\forall ( \operatorname{z} : \operatorname{Runtime} ) , ( \forall ( \operatorname{ops} : \operatorname{List} \operatorname{Operation} ) , ( ( \operatorname{runtimeExecute} \operatorname{z} \operatorname{ops} ) . \operatorname{map} \operatorname{Runtime} . \operatorname{fields} = \operatorname{executeFinite} \operatorname{z} . \operatorname{fields} \operatorname{ops} ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.runtime_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Projecting every partial runtime execution to FiniteFields gives the original finite execution, including failures.

**Theorem 1.3 (arbitrary legal projection).**

$$\forall ( \operatorname{ops} : \operatorname{List} \operatorname{Operation} ) , ( ( \operatorname{Legal} \operatorname{ops} ) \Rightarrow ( ( \operatorname{runtimeRun} \operatorname{ops} ) . \operatorname{map} \operatorname{Runtime} . \operatorname{fields} = ( \operatorname{run} \operatorname{ops} ) . \operatorname{map} ( \operatorname{fun} \operatorname{c} \mapsto \operatorname{c} . \operatorname{source} . \operatorname{finiteFields} ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.arbitrary_legal_projection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Original native prefix reconstruction identifies the finite fields for every legal paid operation history. Source counters remain external.

**Theorem 1.4 (query mode classification).**

$$\forall ( \operatorname{z} : \operatorname{Runtime} ) , ( ( \operatorname{queryMode} \operatorname{z} = . \operatorname{g} \Leftrightarrow \operatorname{z} . \operatorname{fields} . \operatorname{control} = . \operatorname{fourth} ( . \operatorname{active} . \operatorname{p} ) \land \operatorname{z} . \operatorname{mode} = . \operatorname{g} ) \land ( \operatorname{queryMode} \operatorname{z} = . \operatorname{gBeta} \Leftrightarrow \operatorname{z} . \operatorname{fields} . \operatorname{control} = . \operatorname{fourth} ( . \operatorname{active} . \operatorname{beta} ) \land \operatorname{z} . \operatorname{mode} = . \operatorname{gBeta} ) \land ( \operatorname{queryMode} \operatorname{z} = . \operatorname{ordinary} \Leftrightarrow \neg ( \operatorname{z} . \operatorname{fields} . \operatorname{control} = . \operatorname{fourth} ( . \operatorname{active} . \operatorname{p} ) \land \operatorname{z} . \operatorname{mode} = . \operatorname{g} ) \land \neg ( \operatorname{z} . \operatorname{fields} . \operatorname{control} = . \operatorname{fourth} ( . \operatorname{active} . \operatorname{beta} ) \land \operatorname{z} . \operatorname{mode} = . \operatorname{gBeta} ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.query_mode_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A special query requires its matching fourth-segment phase and one-shot mode. All other finite configurations use the ordinary row.

**Theorem 1.5 (original latch activation).**

$$\forall ( \operatorname{n} : \mathbb{N} ) , ( ( 375 \leq \operatorname{n} ) \Rightarrow ( \operatorname{runtimeRun} ( \operatorname{reads} ( \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} ) ) = \operatorname{some} \langle \operatorname{latchedFields} , . \operatorname{accepted} , . \operatorname{g} \rangle \land \operatorname{runtimeRun} ( \operatorname{reads} ( \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} . \operatorname{take} 5 ) ) = \operatorname{some} \langle \operatorname{beforeLatchFields} , . \operatorname{suffix} 4 , . \operatorname{watching} \rangle \land \operatorname{beforeLatchFields} . \operatorname{registers} . \operatorname{snapshot} = \operatorname{none} \land \operatorname{latchedFields} . \operatorname{registers} . \operatorname{snapshot} = \operatorname{some} \langle 1 , 1 , 1 \rangle \land \operatorname{finiteStep} \operatorname{beforeLatchFields} ( . \operatorname{read} 0 ) = \operatorname{some} \operatorname{latchedFields} ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.original_latch_activation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five-letter suffix prefix has no snapshot. The sixth original Read performs the third marker write and latches the snapshot before G becomes active.

**Theorem 1.6 (special transactions).**

$$\forall ( \operatorname{r} : \operatorname{Registers} ) , ( \forall ( \operatorname{mon} : \operatorname{Monitor} ) , ( \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} ( . \operatorname{active} . \operatorname{p} ) , \operatorname{r} \rangle , \operatorname{mon} , . \operatorname{g} \rangle ( . \operatorname{read} 0 ) = \operatorname{some} \langle \langle . \operatorname{fourth} ( . \operatorname{pending} 0 ) , \operatorname{writeMarker} \operatorname{r} 3 0 \rangle , \operatorname{scan} \operatorname{mon} 0 , . \operatorname{ordinary} \rangle \land \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} ( . \operatorname{active} . \operatorname{p} ) , \operatorname{r} \rangle , \operatorname{mon} , . \operatorname{g} \rangle ( . \operatorname{read} 1 ) = \operatorname{some} \langle \langle . \operatorname{fourth} ( . \operatorname{active} . \operatorname{beta} ) , \operatorname{r} \rangle , \operatorname{scan} \operatorname{mon} 1 , . \operatorname{gBeta} \rangle \land \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} ( . \operatorname{active} . \operatorname{beta} ) , \operatorname{r} \rangle , \operatorname{mon} , . \operatorname{gBeta} \rangle ( . \operatorname{read} 0 ) = \operatorname{some} \langle \langle . \operatorname{fourth} ( . \operatorname{active} . \operatorname{p} ) , \operatorname{r} \rangle , \operatorname{scan} \operatorname{mon} 0 , . \operatorname{ordinary} \rangle \land \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} ( . \operatorname{active} . \operatorname{beta} ) , \operatorname{r} \rangle , \operatorname{mon} , . \operatorname{gBeta} \rangle ( . \operatorname{read} 1 ) = \operatorname{some} \langle \langle . \operatorname{fourth} ( . \operatorname{pending} 1 ) , \operatorname{writeMarker} \operatorname{r} 3 1 \rangle , \operatorname{scan} \operatorname{mon} 1 , . \operatorname{ordinary} \rangle ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.special_transactions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four original active transitions give the two special completions, the Gbeta continuation and the return that selects ordinary mode.

**Theorem 1.7 (terminal permissions).**

$$\forall ( \operatorname{r} : \operatorname{Registers} ) , ( \forall ( \operatorname{mon} : \operatorname{Monitor} ) , ( \forall ( \operatorname{m} : \operatorname{Mode} ) , ( \forall ( \operatorname{a} \operatorname{b} \operatorname{x} : \operatorname{Letter} ) , ( \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} ( . \operatorname{pending} \operatorname{a} ) , \operatorname{r} \rangle , \operatorname{mon} , \operatorname{m} \rangle ( . \operatorname{read} \operatorname{x} ) = \operatorname{none} \land ( \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} ( . \operatorname{pending} \operatorname{a} ) , \operatorname{r} \rangle , \operatorname{mon} , \operatorname{m} \rangle ( . \operatorname{stop} \operatorname{b} ) ) . \operatorname{map} \operatorname{Runtime} . \operatorname{fields} = ( \operatorname{if} \operatorname{b} = \operatorname{a} \operatorname{then} \operatorname{some} \langle . \operatorname{fourth} . \operatorname{delivered} , \operatorname{r} \rangle \operatorname{else} \operatorname{none} ) \land \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} . \operatorname{delivered} , \operatorname{r} \rangle , \operatorname{mon} , \operatorname{m} \rangle ( . \operatorname{read} \operatorname{x} ) = \operatorname{none} \land \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} . \operatorname{delivered} , \operatorname{r} \rangle , \operatorname{mon} , \operatorname{m} \rangle ( . \operatorname{stop} \operatorname{b} ) = \operatorname{none} ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.terminal_permissions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pending admits exactly its matching Stop. Pending and delivered reject every Read; delivered also rejects every Stop.

**Theorem 1.8 (exhaustive history modes).**

$$\forall ( \operatorname{ops} : \operatorname{List} \operatorname{Operation} ) , ( \forall ( \operatorname{z} : \operatorname{Runtime} ) , ( ( \operatorname{runtimeRun} \operatorname{ops} = \operatorname{some} \operatorname{z} ) \Rightarrow ( ( \operatorname{z} . \operatorname{mode} = . \operatorname{g} \Rightarrow \exists \operatorname{n} , 375 \leq \operatorname{n} \land \operatorname{ops} = \operatorname{reads} ( \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} ) ) \land ( \operatorname{z} . \operatorname{mode} = . \operatorname{gBeta} \Rightarrow \exists \operatorname{n} , 375 \leq \operatorname{n} \land \operatorname{ops} = \operatorname{reads} ( \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} + + [ 1 ] ) ) \land ( ( \neg \exists \operatorname{n} , 375 \leq \operatorname{n} \land \operatorname{ops} = \operatorname{reads} ( \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} ) ) \Rightarrow ( \neg \exists \operatorname{n} , 375 \leq \operatorname{n} \land \operatorname{ops} = \operatorname{reads} ( \operatorname{blocks} \operatorname{n} + + \operatorname{latchWord} + + [ 1 ] ) ) \Rightarrow \operatorname{queryMode} \operatorname{z} = . \operatorname{ordinary} ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.exhaustive_history_modes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The history invariant restricts G and Gbeta to the recognized whole word and its single beta continuation. Every other successful history queries the ordinary row.

**Theorem 1.9 (special return permanence).**

$$\forall ( \operatorname{r} : \operatorname{Registers} ) , ( \forall ( \operatorname{mon} : \operatorname{Monitor} ) , ( \forall ( \operatorname{ops} : \operatorname{List} \operatorname{Operation} ) , ( \forall ( \operatorname{d} : \operatorname{Runtime} ) , ( ( \operatorname{runtimeExecute} \langle \langle . \operatorname{fourth} ( . \operatorname{active} . \operatorname{beta} ) , \operatorname{r} \rangle , \operatorname{mon} , . \operatorname{gBeta} \rangle ( . \operatorname{read} 0 : : \operatorname{ops} ) = \operatorname{some} \operatorname{d} ) \Rightarrow ( \operatorname{d} . \operatorname{mode} = . \operatorname{ordinary} ) ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.special_return_permanence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Ordinary mode is invariant under every subsequent successful transaction, including the suffix after the original Gbeta alpha return.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.arbitrary_legal_projection`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.exhaustive_history_modes`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.original_latch_activation`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.query_mode_classification`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.runtime_projection`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.special_return_permanence`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.special_transactions`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.terminal_permissions`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFiniteMonitor.whole_word_recognition`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixReconstruction](NativeAcquiredPrefixReconstruction.md)
