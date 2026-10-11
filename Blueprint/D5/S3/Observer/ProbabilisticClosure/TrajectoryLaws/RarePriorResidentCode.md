# RarePriorResidentCode

## Abstract

RarePriorResidentCode

Explicit mixed-radix codecs encode NativeControl, Registers, ThirdSnapshot, FiniteFields, the saturating monitor and one-shot mode. Their runtime has 793800 times 6023 times 4 addresses. A second explicit codec encodes the threshold tag, PC, bit position, candidate and output. Native dictionaries store every runtime-operation key and its original partial successor; service dictionaries store every service-bit key and microstep successor. A third resident dictionary initializes the threshold tag from the original finite query mode, using high for G, low for Gbeta and ordinary otherwise.

Resident code includes all three addressed key and payload tapes, the instruction records, and the saturation, threshold, acceptance and bit-width constants. The interpreter scans key bits sequentially and copies payload bits sequentially. Its row address, bit cursor, accumulator, PC and equality flag have fixed finite bounds. At the selected row, the exact copied payload implements the original runtimeStep or fair-bit microStep. The execution iteration count belongs to the correctness proof and is absent from runtime state.

The complete snapshot serializes ready and synthetic-copy runtimes, service state, current operation, 32 bounded output scratch cells, cursor, PC, table/source/destination addresses, bit position, matching flag and workspace. Fixed-width blocks make this encoding injective. B0 is one fixed witness greater than resident-code length plus complete snapshot width, with B0 at least one; it is independent of prior, horizon and rare mass. All scanner states fit the same snapshot fields. The scratch is a finite output workspace; full-record rendering is supplied separately.

**Theorem 1.1 (charged snapshot bound).**

$$\forall ( \operatorname{s} : \operatorname{MicroSnapshot} ) , ( ( \operatorname{snapshotCode} \operatorname{s} ) . \operatorname{length} = \operatorname{snapshotWidth} \land \operatorname{residentCode} . \operatorname{length} + ( \operatorname{snapshotCode} \operatorname{s} ) . \operatorname{length} < \operatorname{B}0 \land 1 \leq \operatorname{B}0 )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode.charged_snapshot_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each serialized field has fixed width. The budget is one plus resident width plus snapshot width and charges every stored tape and snapshot bit.

**Theorem 1.2 (complete snapshot encoding).**

$$\operatorname{Function} . \operatorname{Injective} \operatorname{snapshotCode}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode.complete_snapshot_encoding` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fixed-width block boundaries recover every scalar field. Sequential recovery of the output blocks recovers the entire bounded output store.

**Theorem 1.3 (bounded scanner correct).**

$$\forall ( \operatorname{k} \operatorname{n} : \mathbb{N} ) , ( \forall ( \operatorname{table} : \operatorname{Fin} \operatorname{k} \Rightarrow \operatorname{Fin} \operatorname{n} ) , ( \forall ( \operatorname{a} : \operatorname{Fin} \operatorname{k} ) , ( \operatorname{scannerResult} ( \operatorname{scannerTicks} \operatorname{table} ( \operatorname{a} . \operatorname{val} * ( \operatorname{k} + 1 ) + \operatorname{k} + 1 + \operatorname{n} + 1 ) ( \operatorname{scannerEntry} \operatorname{a} ) ) = \operatorname{some} ( \operatorname{table} \operatorname{a} ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode.bounded_scanner_correct` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The scanner skips unmatched key rows, reaches the queried row and copies its unary payload bit by bit into the bounded accumulator.

**Theorem 1.4 (installed bounded program).**

$$\forall ( \operatorname{z} : \operatorname{Runtime} ) , ( \forall ( \operatorname{op} : \operatorname{Operation} ) , ( \forall ( \operatorname{s} : \operatorname{Service} ) , ( \forall ( \operatorname{b} : \operatorname{Letter} ) , ( \forall ( \operatorname{base} : \operatorname{MicroSnapshot} ) , ( \operatorname{nativeProgram} \operatorname{z} \operatorname{op} = \operatorname{runtimeStep} \operatorname{z} \operatorname{op} \land \operatorname{serviceProgram} \operatorname{s} \operatorname{b} = \operatorname{some} ( \operatorname{microStep} \operatorname{s} \operatorname{b} ) \land \operatorname{initializationProgram} \operatorname{z} = \operatorname{some} ( \operatorname{entry} ( \operatorname{selectedThreshold} \operatorname{z} ) ) \land ( \forall ( \operatorname{k} \operatorname{n} : \mathbb{N} ) ( \operatorname{hk} : \operatorname{k} \leq \operatorname{runtimeSize} * 4 ) ( \operatorname{hn} : \operatorname{n} \leq \operatorname{runtimeSize} + 1 ) ( \operatorname{q} : \operatorname{Scanner} \operatorname{k} \operatorname{n} ) , \operatorname{residentCode} . \operatorname{length} + ( \operatorname{snapshotCode} ( \operatorname{scannerSnapshot} \operatorname{base} \operatorname{q} \operatorname{hk} \operatorname{hn} ) ) . \operatorname{length} < \operatorname{B}0 ) \land ( \forall ( \operatorname{k} \operatorname{n} : \mathbb{N} ) ( \operatorname{hk} : \operatorname{k} \leq \operatorname{runtimeSize} * 4 ) ( \operatorname{hn} : \operatorname{n} \leq \operatorname{runtimeSize} + 1 ) , \operatorname{Function} . \operatorname{Injective} ( \operatorname{fun} \operatorname{q} : \operatorname{Scanner} \operatorname{k} \operatorname{n} \mapsto \operatorname{snapshotCode} ( \operatorname{scannerSnapshot} \operatorname{base} \operatorname{q} \operatorname{hk} \operatorname{hn} ) ) ) \land ( \forall ( \operatorname{r} : \operatorname{Registers} ) ( \operatorname{mon} : \operatorname{Monitor} ) ( \operatorname{m} : \operatorname{Mode} ) ( \operatorname{a} \operatorname{b} \operatorname{x} : \operatorname{Letter} ) , \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} ( . \operatorname{pending} \operatorname{a} ) , \operatorname{r} \rangle , \operatorname{mon} , \operatorname{m} \rangle ( . \operatorname{read} \operatorname{x} ) = \operatorname{none} \land ( \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} ( . \operatorname{pending} \operatorname{a} ) , \operatorname{r} \rangle , \operatorname{mon} , \operatorname{m} \rangle ( . \operatorname{stop} \operatorname{b} ) ) . \operatorname{map} \operatorname{Runtime} . \operatorname{fields} = ( \operatorname{if} \operatorname{b} = \operatorname{a} \operatorname{then} \operatorname{some} \langle . \operatorname{fourth} . \operatorname{delivered} , \operatorname{r} \rangle \operatorname{else} \operatorname{none} ) \land \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} . \operatorname{delivered} , \operatorname{r} \rangle , \operatorname{mon} , \operatorname{m} \rangle ( . \operatorname{read} \operatorname{x} ) = \operatorname{none} \land \operatorname{runtimeStep} \langle \langle . \operatorname{fourth} . \operatorname{delivered} , \operatorname{r} \rangle , \operatorname{mon} , \operatorname{m} \rangle ( . \operatorname{stop} \operatorname{b} ) = \operatorname{none} ) ) ) ) ) )$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode.installed_bounded_program` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The three proved resident row relations implement original runtime updates, service microsteps and mode-based service initialization. Every scanner state has an injective charged snapshot encoding, and terminal permissions remain original.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode.bounded_scanner_correct`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode.charged_snapshot_bound`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode.complete_snapshot_encoding`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode.installed_bounded_program`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService](RarePriorFairBitService.md)
