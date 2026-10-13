# Physical-bank query and successor writeback

## Abstract

RarePriorLiteralController.LiveProducerWork

The current bank is first copied to the pre tape and then encoded by the literal key carry into the raw unary query. bank_query identifies that query with nativeKey for the bank-encoded Runtime and captured operation. build_key_work preserves the pre, result and old-field work, row slot and offset through the carry phase.

PayloadGood is a proof invariant relating the scanner row and accumulator to a copied unary payload. installed_payload_step reads the installed physical program, establishes the next payload invariant and refines installedGraphStep. The nativeTable appears in this specification; the transition obtains each payload bit from nativeBit on the installed tape.

Writeback alternates a read from the copied result tape and a write to the role-selected bank. writeCheckpoint fixes every already written prefix and retains the remaining bank cells. The write-cycle and write-prefix inductions include the exhausted boundary, and result_drop removes only the optional-result marker before writing the complete successor Runtime.

The displayed endpoint starts at phase nine with bankProbe zero and the complete successful result tape. It reaches phase eleven with exactly the selected successor bank and the opposite bank preserved. Operation, role and outer image context stay fixed, and writeback emits no frame bits. Phase eleven retains work; it does not assert canonical Ready or a complete repeated service cycle.

**Theorem 1.1 (Complete bitwise writeback with a quiet trace).**

$$\forall (\operatorname{s} : \operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{State}), \forall (\operatorname{d} : \operatorname{Runtime}), (\operatorname{s}).\operatorname{phase} = 9 \to (\operatorname{s}).\operatorname{bankProbe} = 0 \to ((\operatorname{s}).\operatorname{result}).\operatorname{tape} = \operatorname{word} (\operatorname{optionalRuntimeCodec} (\operatorname{some} (\operatorname{d}))) \to \exists (\operatorname{t} : \mathbb{N}), \exists (\operatorname{q} : \operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{State}), ((\operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{run} (\operatorname{s}, \operatorname{t}) = \operatorname{q}) \land ((((\operatorname{q}).\operatorname{phase} = 11) \land ((((\operatorname{q}).\operatorname{actual} = (\operatorname{if} (\operatorname{s}).\operatorname{role} \operatorname{then} (\operatorname{s}).\operatorname{actual} \operatorname{else} \operatorname{word} (\operatorname{runtimeCodec} (\operatorname{d})))) \land ((((\operatorname{q}).\operatorname{synthetic} = (\operatorname{if} (\operatorname{s}).\operatorname{role} \operatorname{then} \operatorname{word} (\operatorname{runtimeCodec} (\operatorname{d})) \operatorname{else} (\operatorname{s}).\operatorname{synthetic})) \land ((((\operatorname{q}).\operatorname{operation} = (\operatorname{s}).\operatorname{operation}) \land ((((\operatorname{q}).\operatorname{role} = (\operatorname{s}).\operatorname{role}) \land (((((\operatorname{q}).\operatorname{addressed}).\operatorname{outer} = ((\operatorname{s}).\operatorname{addressed}).\operatorname{outer}) \land (\operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{trace} (\operatorname{s}, \operatorname{t}) = []))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerWork.write_complete` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The two-instruction per-cell schedule writes every Runtime bit, then the exhausted probe retires. The proof keeps both physical banks in the statement and shows the entire output trace is empty during this phase.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerWork.write_complete`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerExecution](LiveProducerExecution.md)
