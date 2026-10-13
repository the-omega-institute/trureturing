# Resident producer and physical current banks

## Abstract

RarePriorLiteralController.LiveProducerSetup

A producer retains the entire inherited address snapshot, native and service key rails, initialization, sampler, native and menu scanners, copied Runtime and Service words, finite stage, operation, ready role, raw service, reset probe, request and commit flags, and both input latches. Its injective code includes every retained component. The static image includes resident opcodes, rail end masks and service menu; the bound charges that image, the original program and the whole retained state together.

The actual and synthetic banks in CurrentBank are raw Boolean tapes. The role selects the sole mutable destination. The pre, query, payload, result and old-field tapes, row key, slot, offset, bank probe and latch, native scanner and resident-opcode motor coexist. Native key and payload bits are fetched from the installed physical tape, while fieldROM taps the copied pre-state. Address arithmetic and control resets remain atomic rail primitives.

The source and fresh-bit ports are distinct. Deterministic stages ignore both ports, and saved_cuts preserves the inherited retained snapshot at every finite cut. Codecs and decoded returned values are external observations, not transition inputs. The prepared producer below starts with a native key for the supplied Runtime; the unprepared physical-bank acquisition is the separate CurrentAcquisition result.

The native-key carry, scanner endpoint and literal Runtime-word copy are successive phases. ScannerSafe rules out a false successful row, graph_terminal handles absorbing outcomes, and motor_return supplies the copied tape at halt. The conclusion preserves addressed context, captured operation and the uncommitted flag through rendering entry. This finite path does not establish repeated full cycles, canonical Ready or a physical resource realization.

**Theorem 1.1 (Native key reaches its copied return word).**

$$\forall (\operatorname{p} : \operatorname{LiveProducer}.\operatorname{State}), \forall (\operatorname{z} : \operatorname{Runtime}), \forall (\operatorname{op} : \operatorname{Operation}), \forall (\operatorname{d} : \operatorname{Runtime}), (\operatorname{p}).\operatorname{stage} = \operatorname{LiveProducer}.\operatorname{Stage}.\operatorname{nativeKey} \to (\operatorname{p}).\operatorname{nativeKey} = \operatorname{keyEntry} (\operatorname{word} (\operatorname{runtimeCodec} (\operatorname{z})), \operatorname{operationCodec} (\operatorname{op})) \to (\operatorname{p}).\operatorname{runtime} = \operatorname{motorEntry} (\operatorname{runtimeSize}+1) \to (\operatorname{p}).\operatorname{operation} = \operatorname{operationCodec} (\operatorname{op}) \to (\operatorname{p}).\operatorname{committed} = \operatorname{false} \to \operatorname{runtimeStep} (\operatorname{z}, \operatorname{op}) = \operatorname{some} (\operatorname{d}) \to \exists (\operatorname{t} : \mathbb{N}), \exists (\operatorname{a} : \operatorname{LiveProducer}.\operatorname{State}), ((\operatorname{LiveProducer}.\operatorname{run} (\operatorname{p}, 0, 0, \operatorname{t}) = \operatorname{a}) \land ((((\operatorname{a}).\operatorname{stage} = \operatorname{LiveProducer}.\operatorname{Stage}.\operatorname{render}) \land (((((\operatorname{a}).\operatorname{runtime}).\operatorname{tape} = \operatorname{word} (\operatorname{optionalRuntimeCodec} (\operatorname{some} (\operatorname{d})))) \land ((((\operatorname{a}).\operatorname{addressed} = (\operatorname{p}).\operatorname{addressed}) \land ((((\operatorname{a}).\operatorname{operation} = \operatorname{operationCodec} (\operatorname{op})) \land ((\operatorname{a}).\operatorname{committed} = \operatorname{false}))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerSetup.native_render` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A successful original runtimeStep is implemented from the stated native-key entry. The scanner result and literal tape copy produce the complete optional Runtime word; neither a successful scan nor a typed Runtime value is supplied as an instruction input.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerSetup.native_render`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/TransfersAddress](TransfersAddress.md)
