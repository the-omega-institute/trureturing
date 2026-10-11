# Serial scanner execution

## Abstract

Finite scanner flights realize serial adaptive service and native operation returns.

The concrete carrier is the existing finite seven-bit packet and the existing finite service state. Consecutive coordinates of one external fair-bit stream are grouped into packets only for analysis; the service continues to read one bit at a time through its installed bit transition.

The accepted stream is obtained by the generic first-acceptance restart construction. Its first-hit index, unused suffix and packet number are external analysis coordinates. They are not registers, a readable random tape, a new operation, or an uncharged scanner.

The repeated theorem gives the complete iid conditional accepted-packet law and, outside one common null event, identifies every ready-entry execution with the existing reset/bit/compare graph. The finite scanner and adaptive runtime simulation are given below. Full renderer and interpreter charging, COMPLETE membership, the two original compatibility statements and inf-sup risks remain separate obligations.

**Definition 1.1 (Vector to packet).**

$$\forall (\operatorname{v} : \operatorname{Fin} (7) \Rightarrow \operatorname{Letter}) , \operatorname{vectorPacket} (\operatorname{v}) = \langle\operatorname{v} (0),\operatorname{v} (1),\operatorname{v} (2),\operatorname{v} (3),\operatorname{v} (4),\operatorname{v} (5),\operatorname{v} (6)\rangle$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.vectorPacket` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seven finite coordinates are packed into the existing seven-bit packet carrier.

**Definition 1.2 (External stream packetization).**

$$\forall (\operatorname{omega} : \mathbb{N} \Rightarrow \operatorname{Letter}) , \forall (\operatorname{n} : \mathbb{N}) , \operatorname{packetize} (\operatorname{omega} , \operatorname{n}) = \operatorname{vectorPacket} ((\operatorname{fun} \operatorname{i} : \operatorname{Fin} (7) \mapsto \operatorname{omega} (\operatorname{n}*7+\operatorname{i}.\operatorname{val})))$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.packetize` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The nth packet reads seven consecutive coordinates from one external bit stream.

**Definition 1.3 (External fair-bit law).**

$$\operatorname{freshBitLaw} = \operatorname{Measure}.\operatorname{infinitePi} ((\operatorname{fun} \operatorname{index} : \mathbb{N} \mapsto \operatorname{bernoulliMeasure} (0 , 1 , \operatorname{fairParameter})))$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.freshBitLaw` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source law is the infinite product of the fair Bernoulli law on the existing bit carrier.

**Definition 1.4 (Accepted finite packets).**

$$\operatorname{acceptedPackets} = \{\operatorname{p} : \operatorname{Packet} \Vert\operatorname{packetEquiv} (\operatorname{p}).\operatorname{val} < 100\}$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.acceptedPackets` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exactly the existing candidate addresses below 100 are accepted.

**Theorem 1.5 (Positive acceptance).**

$$\operatorname{packetLaw} (\operatorname{acceptedPackets}) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.acceptance_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An original positive-mass packet lies in the acceptance set. The serial adaptive runtime law directly uses this supplier for the conditional packet law and measurable repeated draw.

**Definition 1.6 (Accepted packet stream).**

$$\forall (\operatorname{omega} : \mathbb{N} \Rightarrow \operatorname{Letter}) , \forall (\operatorname{n} : \mathbb{N}) , \operatorname{acceptedStream} (\operatorname{omega} , \operatorname{n}) = \operatorname{FreshServiceRestart}.\operatorname{draws} (\operatorname{acceptedPackets} , \operatorname{fallbackPacket} , \operatorname{packetize} (\operatorname{omega}) , \operatorname{n})$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.acceptedStream` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Repeated accepted packets are selected by the generic suffix-restart construction.

**Definition 1.7 (Ready-entry execution).**

$$\forall (\operatorname{t} : \operatorname{Threshold}) , \forall (\operatorname{omega} : \mathbb{N} \Rightarrow \operatorname{Letter}) , \forall (\operatorname{k} : \mathbb{N}) , \operatorname{executedReadyService} (\operatorname{t} , \operatorname{omega} , \operatorname{k}) = \operatorname{match} \operatorname{FreshServiceRestart}.\operatorname{firstHit} (\operatorname{acceptedPackets} , \operatorname{FreshServiceRestart}.\operatorname{unused} (\operatorname{acceptedPackets} , \operatorname{fallbackPacket} , \operatorname{k} , \operatorname{packetize} (\operatorname{omega}))) \operatorname{with} | \operatorname{none} \Rightarrow \operatorname{none} | \operatorname{some} \operatorname{n} \Rightarrow \operatorname{some} (\operatorname{trialRun} (\operatorname{entry} (\operatorname{t}) , \operatorname{FreshServiceRestart}.\operatorname{unused} (\operatorname{acceptedPackets} , \operatorname{fallbackPacket} , \operatorname{k} , \operatorname{packetize} (\operatorname{omega})) , \operatorname{successor} (\operatorname{n})))$$

*Formalization.* `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.executedReadyService` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each repeated service executes the existing trialRun from its prescribed reset entry until the first accepted packet.

**Theorem 1.8 (Repeated service law).**

$$\operatorname{Measure}.\operatorname{map} (\operatorname{acceptedStream} , \operatorname{freshBitLaw}) = \operatorname{Measure}.\operatorname{infinitePi} ((\operatorname{fun} \operatorname{index} : \mathbb{N} \mapsto \operatorname{ProbabilityTheory}.\operatorname{cond} (\operatorname{packetLaw} , \operatorname{acceptedPackets}))) \land (\operatorname{ae} \operatorname{omega} \operatorname{under} \operatorname{freshBitLaw}, \forall (\operatorname{k} : \mathbb{N}) , \forall (\operatorname{t} : \operatorname{Threshold}) , \operatorname{executedReadyService} (\operatorname{t} , \operatorname{omega} , \operatorname{k}) = \operatorname{some} (\langle\operatorname{t},.\operatorname{returned},6,\operatorname{packetEquiv} (\operatorname{acceptedStream} (\operatorname{omega} , \operatorname{k})),\operatorname{if} (\operatorname{packetEquiv} (\operatorname{acceptedStream} (\operatorname{omega} , \operatorname{k})).\operatorname{val} < \operatorname{threshold} (\operatorname{t}).\operatorname{val} , 0 , 1)\rangle))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.repeated_fresh_bit_service` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

One external stream has the complete conditional accepted-packet product law, and every ready-entry execution returns the existing threshold result outside one common null event.

A Flight contains the existing finite scanner and a finite countdown. The countdown ceiling is k times (k plus one) plus n plus one for a k-key, n-payload table. The entry countdown depends only on the finite query address. Each flight instruction advances the installed instruction graph once and decreases this stored countdown. At zero it reads the scanner result. The invariant holds for every flight, every table and every permitted internal cut, including malformed scanner states.

ServiceMachine has ready, scanning and fault constructors. Every constructor retains its finite Runtime and Service. Scanning additionally retains the complete Flight for the existing 43008-key, 21504-payload service dictionary. A ready bit instruction requests exactly one external bit; reset and comparison supply the deterministic value zero, and the scanner consumes no source data. The input bit is contained in the finite table query. Returned and fault states are absorbing. A launch followed by the stored finite countdown and one return instruction implements the original microStep, for every service state.

Serial trial scheduling executes reset, each required bit and comparison through these scanner flights. A paused bit service consumes precisely its remaining bits. Comparison and returned services consume no bits. Packet lists, first-hit indices, suffixes and service numbers are external execution coordinates; the machine has no packet input port, counter of rejected trials, tape position or readable random archive. Its executable randomness port is the single bitRequest instruction.

Initialization and native operation updates execute the existing initialization and native dictionaries through the same finite flight evaluator. The adaptive threshold is selected from the retained Runtime. Its source control, registers, saturating monitor and mode determine that selection. Pending performs only the unique matching Stop; delivered has no next operation. These cases include all finite control states, the seed prelude, partial original transactions and both fourth phases. The serial recurrence starts from every Runtime, rather than only a selected long history.

One common full-measure event of the original external fair-bit stream supports all services and all adaptive operation-return prefixes. The complete infinite serial runtime law equals the pushforward of the same conditional accepted-packet product law under the finite adaptive recurrence. The proof first establishes the actual scanner-flight invariant and serial trial simulation, then uses both the return and product-law conjuncts of repeated_fresh_bit_service. This is an identity of runtime paths with pending and delivered states, retaining service nonreturn as none on the exceptional source paths.

Explicit mixed-radix codecs include the constructor, retained runtime, service PC, candidate, bit position, scanner registers and countdown. A fixed-width unary encoding is injective on every ready, paused scanning and fault state. The localBound expression is B0 plus machineSize plus one and pays the original complete MicroSnapshot alongside this additional local machine state. It is independent of prior, horizon and rejection count. The finite construction does not require materializing the dictionaries. Initialization and native flights use other table dimensions; this local service bound does not include their stored countdowns or the unified scheduling state. Full renderer and controller-interpreter code accounting, serial service commitment into the unified instruction controller, identity to the original generated marked/full transcript, the two original compatibility statements, COMPLETE membership and original radii/Phi/U remain further obligations.

**Theorem 1.9 (Serial adaptive execution).**

$$(\forall (\operatorname{k} : \mathbb{N}) , \forall (\operatorname{n} : \mathbb{N}) , \forall (\operatorname{table} : \operatorname{Fin} (\operatorname{k}) \Rightarrow \operatorname{Fin} (\operatorname{n})) , \forall (\operatorname{s} : \operatorname{Flight} (\operatorname{k} , \operatorname{n})) , \forall (\operatorname{m} : \mathbb{N}) , (\operatorname{m} \leq (\operatorname{s}).\operatorname{remaining}.\operatorname{val} \Rightarrow ((\operatorname{flightRun} (\operatorname{table} , \operatorname{s} , \operatorname{m})).\operatorname{scanner} = \operatorname{iterate} (\operatorname{installedGraphStep} (\operatorname{table}) , \operatorname{m} , (\operatorname{s}).\operatorname{scanner}) \land (\operatorname{flightRun} (\operatorname{table} , \operatorname{s} , \operatorname{m})).\operatorname{remaining}.\operatorname{val} = (\operatorname{s}).\operatorname{remaining}.\operatorname{val}-\operatorname{m})) \land \forall (\operatorname{z} : \operatorname{Runtime}) , \forall (\operatorname{s} : \operatorname{Service}) , \forall (\operatorname{b} : \operatorname{Letter}) , \operatorname{let} \operatorname{x} : \operatorname{Letter} = \operatorname{if} ((\operatorname{s}).\operatorname{pc} = \operatorname{PC}.\operatorname{bit} , \operatorname{b} , 0) \operatorname{in} \operatorname{let} \operatorname{f} : \operatorname{Flight} (43008 , 21504) = \operatorname{flightEntry} (\operatorname{bitKeyCodec} ((\operatorname{s},\operatorname{x}))) \operatorname{in} \operatorname{machineRun} (\operatorname{machineStep} (\operatorname{ServiceMachine}.\operatorname{ready} (\operatorname{z} , \operatorname{s}) , \operatorname{b}) , (\operatorname{f}).\operatorname{remaining}.\operatorname{val}+1) = \operatorname{ServiceMachine}.\operatorname{ready} (\operatorname{z} , \operatorname{microStep} (\operatorname{s} , \operatorname{b})) \land \forall (\operatorname{q} : \operatorname{ServiceMachine}) , \forall (\operatorname{a} : \operatorname{Letter}) , \forall (\operatorname{b} : \operatorname{Letter}) , (\operatorname{bitRequest} (\operatorname{q}) = \operatorname{false} \Rightarrow \operatorname{machineStep} (\operatorname{q} , \operatorname{a}) = \operatorname{machineStep} (\operatorname{q} , \operatorname{b})) \land \forall (\operatorname{base} : \operatorname{MicroSnapshot}) , \forall (\operatorname{q} : \operatorname{ServiceMachine}) , ((\operatorname{machineCode} (\operatorname{q})).\operatorname{length} = \operatorname{machineSize} \land (\operatorname{residentCode}).\operatorname{length}+(\operatorname{snapshotCode} (\operatorname{base})).\operatorname{length}+(\operatorname{machineCode} (\operatorname{q})).\operatorname{length} < \operatorname{localBound}) \land \operatorname{Function}.\operatorname{Injective} (\operatorname{machineCode}) \land \forall (\operatorname{s} : \operatorname{Service}) , \forall (\operatorname{p} : \operatorname{Packet}) , \operatorname{serialTrial} (\operatorname{s} , \operatorname{p}) = \operatorname{some} (\operatorname{finishTrial} (\operatorname{s} , \operatorname{p})) \land \forall (\operatorname{z} : \operatorname{Runtime}) , \operatorname{Measure}.\operatorname{map} (\operatorname{serialStates} (\operatorname{z}) , \operatorname{freshBitLaw}) = \operatorname{packetRuntimeLaw} (\operatorname{z}) \land \operatorname{ae} \operatorname{omega} \operatorname{under} \operatorname{freshBitLaw}, \forall (\operatorname{z} : \operatorname{Runtime}) , (\forall (\operatorname{n} : \mathbb{N}) , \operatorname{serialStates} (\operatorname{z} , \operatorname{omega} , \operatorname{n}) = \operatorname{some} (\operatorname{packetStates} (\operatorname{z} , \operatorname{acceptedStream} (\operatorname{omega}) , \operatorname{n})) \land \forall (\operatorname{k} : \mathbb{N}) , \operatorname{serialOperation} (\operatorname{packetStates} (\operatorname{z} , \operatorname{acceptedStream} (\operatorname{omega}) , \operatorname{k}) , \operatorname{omega} , \operatorname{k}) = \operatorname{packetOperation} (\operatorname{packetStates} (\operatorname{z} , \operatorname{acceptedStream} (\operatorname{omega}) , \operatorname{k}) , \operatorname{acceptedStream} (\operatorname{omega} , \operatorname{k}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.serial_adaptive_execution` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The eight clauses give the flight invariant, one instruction return, port independence at every nonrequesting state, local charge, injective encoding, paused trial simulation, whole adaptive runtime law and common-event operation-return simulation.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.acceptance_positive`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.acceptedPackets`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.acceptedStream`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.executedReadyService`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.freshBitLaw`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.packetize`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.repeated_fresh_bit_service`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.serial_adaptive_execution`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.vectorPacket`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart](FreshServiceRestart.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService](RarePriorFairBitService.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFullFields](RarePriorFullFields.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode](RarePriorResidentCode.md)
