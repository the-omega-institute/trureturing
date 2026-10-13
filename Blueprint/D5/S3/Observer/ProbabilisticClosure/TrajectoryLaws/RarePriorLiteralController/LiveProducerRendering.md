# Six original frame words and selected-bank commit

## Abstract

RarePriorLiteralController.LiveProducerRendering

The installed scanner cycles pay for resident-opcode copying before each native scan step. scan_exit combines the scanner refinement and PayloadGood invariant with the successful native result. result_exit and fields_exit then copy the successful payload and the original pre-state fields; prepare_event reaches the original event-row key.

Each row key is fieldsCodec times twenty-four plus the captured operation times six plus the slot. The address motor reads the installed frame bit at the current offset. row_emit and offset_emit advance through the entire frameWidth. finish_frame completes the current frame at phase eight while preserving its slot; render_remaining advances between slots, and render_all orders all six frame words. These are actual transition and trace equalities; the chronological slot and offset coordinates remain external proof parameters.

The result below requires rendering entry at phase five, slot and offset zero, the exact encoded old fields, matching row key, captured operation, installed program and the complete successful successor-result tape. It first emits the flattened six frame codes in increasing slot order and then performs quiet selected-bank writeback. The opposite bank, operation, role and outer installation context are retained.

preparing_quiet excludes output before rendering. For an execution that reaches phase eleven, retired_no_fault excludes phase twelve at every cut. render_commit preserves the outer installation context at its endpoint. Phase eleven is a retained-work endpoint; a canonical Ready reset, repeated full cycles, live fresh service, full-tail readout, COMPLETE membership and the full-class risk, radius and threshold claims are outside this result.

**Theorem 1.1 (Exact six-frame stream followed by bank writeback).**

$$\forall (\operatorname{s} : \operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{State}), \forall (\operatorname{z} : \operatorname{Runtime}), \forall (\operatorname{d} : \operatorname{Runtime}), \forall (\operatorname{op} : \operatorname{Operation}), (\operatorname{s}).\operatorname{phase} = 5 \to (\operatorname{s}).\operatorname{operation} = \operatorname{operationCodec} (\operatorname{op}) \to ((((\operatorname{s}).\operatorname{addressed}).\operatorname{outer}).\operatorname{installation}).\operatorname{tape} = \operatorname{programTape} \to (\operatorname{s}).\operatorname{row} = \operatorname{keyEntry} (\operatorname{word} (\operatorname{fieldsCodec} ((\operatorname{z}).\operatorname{fields})), \langle((\operatorname{s}).\operatorname{operation}).\operatorname{val}*6+((\operatorname{s}).\operatorname{slot}).\operatorname{val}\rangle) \to ((\operatorname{s}).\operatorname{fields}).\operatorname{tape} = \operatorname{word} (\operatorname{fieldsCodec} ((\operatorname{z}).\operatorname{fields})) \to ((\operatorname{s}).\operatorname{offset}).\operatorname{val} = 0 \to (\operatorname{s}).\operatorname{slot} = 0 \to ((\operatorname{s}).\operatorname{result}).\operatorname{tape} = \operatorname{word} (\operatorname{optionalRuntimeCodec} (\operatorname{some} (\operatorname{d}))) \to \exists (\operatorname{t} : \mathbb{N}), \exists (\operatorname{q} : \operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{State}), ((\operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{run} (\operatorname{s}, \operatorname{t}) = \operatorname{q}) \land ((((\operatorname{q}).\operatorname{phase} = 11) \land ((((\operatorname{q}).\operatorname{actual} = (\operatorname{if} (\operatorname{s}).\operatorname{role} \operatorname{then} (\operatorname{s}).\operatorname{actual} \operatorname{else} \operatorname{word} (\operatorname{runtimeCodec} (\operatorname{d})))) \land ((((\operatorname{q}).\operatorname{synthetic} = (\operatorname{if} (\operatorname{s}).\operatorname{role} \operatorname{then} \operatorname{word} (\operatorname{runtimeCodec} (\operatorname{d})) \operatorname{else} (\operatorname{s}).\operatorname{synthetic})) \land ((((\operatorname{q}).\operatorname{operation} = (\operatorname{s}).\operatorname{operation}) \land ((((\operatorname{q}).\operatorname{role} = (\operatorname{s}).\operatorname{role}) \land (((((\operatorname{q}).\operatorname{addressed}).\operatorname{outer} = ((\operatorname{s}).\operatorname{addressed}).\operatorname{outer}) \land (\operatorname{LiveProducer}.\operatorname{CurrentBank}.\operatorname{trace} (\operatorname{s}, \operatorname{t}) = (\operatorname{List}.\operatorname{ofFn} ((\operatorname{fun} \operatorname{slot} : \operatorname{Fin} (6) \mapsto \operatorname{bitCode} (\operatorname{frameCodec} (\operatorname{eventROM} ((\operatorname{z}).\operatorname{fields}, \operatorname{op}, \operatorname{slot})))))).\operatorname{flatten}))))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerRendering.render_commit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The frame sequence is determined by the same original fields and operation as the row key. Its full bit trace survives concatenation with the quiet writeback trace, and both bank equations remain in the conclusion.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerRendering.render_commit`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerWork](LiveProducerWork.md)
