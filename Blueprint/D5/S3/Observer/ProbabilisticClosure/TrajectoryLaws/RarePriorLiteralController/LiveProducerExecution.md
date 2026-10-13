# Captured operations and native key execution

## Abstract

RarePriorLiteralController.LiveProducerExecution

A prepared transaction uses the inherited actual Runtime and captured Operation to execute the native dictionary, copy its full return word, address the selected original frame bit, emit that bit and commit the tagged operation. acquisition_commit starts with the actual source-request instruction and retains its own Operation.read value. The passive-port law keeps unrelated source and fresh values out of deterministic steps.

Returns means that a finite run reaches the returned stage. The rank is the least such finite time and is used only in external analysis: it is not a stored clock or instruction input. rank_step strictly decreases before return, and no_fault excludes fault on every cut of a returning execution. These claims are conditional on the returning path; they do not prove totality of every producer state.

For CurrentBank, a carry increment writes exactly the newly reached raw unary query cell. The build-key induction identifies that tape with the encoded native key, while build_exit connects the terminal carry to scanner entry and resident opcode loading. native_bit_correct, opcode_rom, opcode_decode and native_scan_refines connect installed tape reads to the existing nativeTable specification.

The frame law below holds for every state and iteration count, including zero and malformed key rails. It preserves both banks, the captured operation, inherited addressed context, opcode motor and role throughout key building. Only the key and query work can change. This law supplies the physical-bank fetch bridge without replacing a tape read by a decoded Runtime operation.

**Theorem 1.1 (Key building preserves the surrounding banks and controls).**

$$\forall (\operatorname{s} : \operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{State}), \forall (\operatorname{n} : \mathbb{N}), ((((\operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{buildKey})^{[\operatorname{n}]} \operatorname{s}).\operatorname{actual} = (\operatorname{s}).\operatorname{actual}) \land (((((\operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{buildKey})^{[\operatorname{n}]} \operatorname{s}).\operatorname{synthetic} = (\operatorname{s}).\operatorname{synthetic}) \land (((((\operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{buildKey})^{[\operatorname{n}]} \operatorname{s}).\operatorname{operation} = (\operatorname{s}).\operatorname{operation}) \land (((((\operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{buildKey})^{[\operatorname{n}]} \operatorname{s}).\operatorname{addressed} = (\operatorname{s}).\operatorname{addressed}) \land (((((\operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{buildKey})^{[\operatorname{n}]} \operatorname{s}).\operatorname{opcodes} = (\operatorname{s}).\operatorname{opcodes}) \land (((\operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{buildKey})^{[\operatorname{n}]} \operatorname{s}).\operatorname{role} = (\operatorname{s}).\operatorname{role}))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerExecution.build_key_frame` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each literal carry step preserves the six displayed context components. Induction composes that step relation through every finite iteration; the native fetch uses it together with the independently proved key and query relations.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerExecution.build_key_frame`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerSetup](LiveProducerSetup.md)
