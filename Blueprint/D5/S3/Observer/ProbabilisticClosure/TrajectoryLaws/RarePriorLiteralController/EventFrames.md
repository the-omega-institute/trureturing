# Finite original events and paused frame copies

## Abstract

RarePriorLiteralController.EventFrames

The event representation records finite completion indices and preserves the original event block. Copy checkpoints specify every residual instruction cut, so frame decoding and lawful history replay refer to the same original fields and operations.

**Theorem 1.1 (Exact original six-slot ROM).**

$$\forall (\operatorname{f} : \operatorname{FiniteFields}), \forall (\operatorname{op} : \operatorname{Operation}), (((\operatorname{eventBlock} (\operatorname{f}, \operatorname{op})).\operatorname{length}\leq6) \land (((\forall (\operatorname{i} : \mathbb{N}), \forall (\operatorname{b} : \operatorname{Letter}), \operatorname{OriginalEvent}.\operatorname{completed} (\operatorname{i}, \operatorname{b}) \in \operatorname{eventBlock} (\operatorname{f}, \operatorname{op}) \implies \operatorname{i}<4) \land (\operatorname{List}.\operatorname{map} (\operatorname{original}, \operatorname{List}.\operatorname{filterMap} (\operatorname{id}, \operatorname{List}.\operatorname{ofFn} (\operatorname{eventROM} (\operatorname{f}, \operatorname{op})))) = \operatorname{eventBlock} (\operatorname{f}, \operatorname{op})))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames.six_slot_original_events` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite field state and operation, the original block has at most six events, every emitted completion index is below four, and the embedded present ROM slots equal that exact block.

**Theorem 1.2 (Every paused tape transfer).**

$$\forall (\operatorname{w} : \mathbb{N}), \forall (\operatorname{rom} : \operatorname{Fin} (\operatorname{w}) \to \operatorname{Bool}), ((\forall (\operatorname{m} : \mathbb{N}), \forall (\operatorname{hm} : \operatorname{m}\leq\operatorname{w}), \forall (\operatorname{r} : \mathbb{N}), ((\operatorname{copyRun} (\operatorname{rom}, \operatorname{copyEntry} (\operatorname{w}), 4*\operatorname{m}+\operatorname{r}) = \operatorname{copyRun} (\operatorname{rom}, \operatorname{copyCheckpoint} (\operatorname{rom}, \operatorname{m}, \operatorname{hm}), \operatorname{r})) \land (\operatorname{copyTrace} (\operatorname{rom}, \operatorname{copyEntry} (\operatorname{w}), 4*\operatorname{m}+\operatorname{r}) = \operatorname{List}.\operatorname{ofFn} ((\operatorname{fun} \operatorname{i} : \operatorname{Fin} (\operatorname{m}) \mapsto \operatorname{rom} (\operatorname{Fin}.\operatorname{castLE} (\operatorname{hm}, \operatorname{i})))) ++ \operatorname{copyTrace} (\operatorname{rom}, \operatorname{copyCheckpoint} (\operatorname{rom}, \operatorname{m}, \operatorname{hm}), \operatorname{r})))) \land ((((\operatorname{copyRun} (\operatorname{rom}, \operatorname{copyEntry} (\operatorname{w}), 4*\operatorname{w})).\operatorname{tape} = \operatorname{rom}) \land (\forall (\operatorname{n} : \mathbb{N}), \operatorname{copyRun} (\operatorname{rom}, \operatorname{copyEntry} (\operatorname{w}), 4*\operatorname{w}+1+\operatorname{n}) = \{\operatorname{copyCheckpoint} (\operatorname{rom}, \operatorname{w}, \operatorname{le}_{\operatorname{rfl}}) \operatorname{with} \operatorname{pc} := \operatorname{CopyPC}.\operatorname{halt}\}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames.paused_copy_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After m complete four-instruction transfers, all subsequent internal states and observations equal execution from the exact prefix checkpoint. At the full width the scratch equals the ROM, and the exhausted instruction halts permanently.

**Theorem 1.3 (Current original frame output).**

$$\forall (\operatorname{f} : \operatorname{FiniteFields}), \forall (\operatorname{op} : \operatorname{Operation}), ((\forall (\operatorname{slot} : \operatorname{Fin} (6)), ((\operatorname{copyTrace} (\operatorname{frameTape} (\operatorname{eventROM} (\operatorname{f}, \operatorname{op}, \operatorname{slot})), \operatorname{renderFrame}, 4*\operatorname{frameWidth}) = \operatorname{bitCode} (\operatorname{frameCodec} (\operatorname{eventROM} (\operatorname{f}, \operatorname{op}, \operatorname{slot})))) \land ((\operatorname{frameRun} (\operatorname{f}, \operatorname{op}, \operatorname{slot}, 4*\operatorname{frameWidth})).\operatorname{tape} = \operatorname{frameTape} (\operatorname{eventROM} (\operatorname{f}, \operatorname{op}, \operatorname{slot}))))) \land (\operatorname{List}.\operatorname{map} (\operatorname{original}, \operatorname{List}.\operatorname{filterMap} (\operatorname{id}, \operatorname{List}.\operatorname{ofFn} ((\operatorname{fun} \operatorname{slot} : \operatorname{Fin} (6) \mapsto \operatorname{decodeFrame} (\operatorname{copyTrace} (\operatorname{frameTape} (\operatorname{eventROM} (\operatorname{f}, \operatorname{op}, \operatorname{slot})), \operatorname{renderFrame}, 4*\operatorname{frameWidth})))))) = \operatorname{eventBlock} (\operatorname{f}, \operatorname{op})))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames.streamed_original_events` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each actual copy trace emits the complete code of its selected finite frame and retains that tape. Decoding the six external frame traces gives exactly the original event block.

**Theorem 1.4 (Charged installation and current frames).**

$$\forall (\operatorname{s} : \operatorname{RenderSnapshot}), ((\operatorname{Function}.\operatorname{Injective} (\operatorname{snapshot})) \land (((\forall (\operatorname{q} : \operatorname{RenderSnapshot}), (\operatorname{programImage}).\operatorname{length}+(\operatorname{snapshot} (\operatorname{q})).\operatorname{length}<\operatorname{rendererBound}) \land (((\operatorname{installed} (\operatorname{s}) = (\operatorname{installStep})^{[4*\operatorname{programWidth}]} \{\operatorname{s} \operatorname{with} \operatorname{installation} := \operatorname{copyEntry} (\operatorname{programWidth})\}) \land ((((((\operatorname{installStep})^{[4*\operatorname{programWidth}]} \{\operatorname{s} \operatorname{with} \operatorname{installation} := \operatorname{copyEntry} (\operatorname{programWidth})\}).\operatorname{installation}).\operatorname{tape} = \operatorname{programTape}) \land (((\forall (\operatorname{slot} : \operatorname{Fin} (6)), \forall (\operatorname{m} : \mathbb{N}), \forall (\operatorname{hm} : \operatorname{m}\leq\operatorname{frameWidth}), \forall (\operatorname{r} : \mathbb{N}), ((\operatorname{frameStep} (\operatorname{slot}))^{[4*\operatorname{m}+\operatorname{r}]} \{\operatorname{installed} (\operatorname{s}) \operatorname{with} \operatorname{frame} := \operatorname{renderFrame}\}).\operatorname{frame} = \operatorname{copyRun} (\operatorname{frameTape} (\operatorname{eventROM} ((((\operatorname{s}).\operatorname{retained}).\operatorname{pre}).\operatorname{fields}, ((\operatorname{s}).\operatorname{retained}).\operatorname{operation}, \operatorname{slot})), \operatorname{copyCheckpoint} (\operatorname{frameTape} (\operatorname{eventROM} ((((\operatorname{s}).\operatorname{retained}).\operatorname{pre}).\operatorname{fields}, ((\operatorname{s}).\operatorname{retained}).\operatorname{operation}, \operatorname{slot})), \operatorname{m}, \operatorname{hm}), \operatorname{r})) \land (\operatorname{List}.\operatorname{map} (\operatorname{original}, \operatorname{List}.\operatorname{filterMap} (\operatorname{id}, \operatorname{List}.\operatorname{ofFn} ((\operatorname{fun} \operatorname{slot} : \operatorname{Fin} (6) \mapsto \operatorname{decodeFrame} (\operatorname{copyTrace} (\operatorname{installedFrameROM} (\operatorname{installed} (\operatorname{s}), \operatorname{slot}), \operatorname{renderFrame}, 4*\operatorname{frameWidth})))))) = \operatorname{eventBlock} ((((\operatorname{s}).\operatorname{retained}).\operatorname{pre}).\operatorname{fields}, ((\operatorname{s}).\operatorname{retained}).\operatorname{operation})))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames.charged_installed_frames` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete snapshot encoding is injective and every value fits the fixed budget. The loader installs the actual image tape. Current-frame instructions read that installed image, satisfy the paused invariant with retained context and emit the exact original block under finite macro addressing.

**Theorem 1.5 (Original source-history replay).**

$$\forall (\operatorname{c} : \operatorname{AcquiredNativeState}), \forall (\operatorname{d} : \operatorname{AcquiredNativeState}), \forall (\operatorname{omega} : \operatorname{Stream}), \forall (\operatorname{n} : \mathbb{N}), \forall (\operatorname{k} : \mathbb{N}), \forall (\operatorname{ops} : \operatorname{List} (\operatorname{Operation})), \operatorname{nativeDrive} (\operatorname{c}, \operatorname{omega}, \operatorname{n}) = \operatorname{some} ((\operatorname{ops},\operatorname{d},\operatorname{k})) \implies ((\operatorname{fullTranscript} (\operatorname{c}, \operatorname{omega}, \operatorname{n}) = \operatorname{some} ((\operatorname{ops},((\operatorname{d}).\operatorname{source}).\operatorname{finiteFields},\operatorname{streamedBlocks} (((\operatorname{c}).\operatorname{source}).\operatorname{finiteFields}, \operatorname{ops})))) \land (\operatorname{List}.\operatorname{foldl} (\operatorname{replayBlock}, ((\operatorname{c}).\operatorname{source}).\operatorname{finiteFields}, \operatorname{streamedBlocks} (((\operatorname{c}).\operatorname{source}).\operatorname{finiteFields}, \operatorname{ops})) = ((\operatorname{d}).\operatorname{source}).\operatorname{finiteFields}))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames.streamed_original_history` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lawful nativeDrive prefix, the streamed frame blocks reconstruct the original full output and replay to its actual finite fields. The operations and iteration indices are external proof coordinates, not retained machine inputs.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames.charged_installed_frames`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames.paused_copy_refinement`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames.six_slot_original_events`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames.streamed_original_events`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames.streamed_original_history`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual](../NativeFullResidual.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode](../RarePriorResidentCode.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution](../RarePriorSerialExecution.md)
