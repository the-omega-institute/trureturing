# Encoded-head finite ROM execution

## Abstract

RarePriorLiteralController.EncodedHead

The head is an encoded finite tape. Its literal scan, carry, read, write and emit instructions implement the ROM copy checkpoints, including paused cuts and permanent halt at the exhausted width.

**Theorem 1.1 (Encoded head at every paused instruction).**

$$\forall (\operatorname{w} : \mathbb{N}), \forall (\operatorname{rom} : \operatorname{Fin} (\operatorname{w}) \to \operatorname{Bool}), ((\forall (\operatorname{m} : \mathbb{N}), \forall (\operatorname{hm} : \operatorname{m}\leq\operatorname{w}), \forall (\operatorname{r} : \mathbb{N}), ((\operatorname{motorRun} (\operatorname{rom}, \operatorname{motorEntry} (\operatorname{w}), \operatorname{motorTime} (\operatorname{m})+\operatorname{r}) = \operatorname{motorRun} (\operatorname{rom}, \operatorname{motorCheckpoint} (\operatorname{rom}, \operatorname{m}, \operatorname{hm}), \operatorname{r})) \land (\operatorname{motorTrace} (\operatorname{rom}, \operatorname{motorEntry} (\operatorname{w}), \operatorname{motorTime} (\operatorname{m})+\operatorname{r}) = \operatorname{copyTrace} (\operatorname{rom}, \operatorname{copyEntry} (\operatorname{w}), 4*\operatorname{m}) ++ \operatorname{motorTrace} (\operatorname{rom}, \operatorname{motorCheckpoint} (\operatorname{rom}, \operatorname{m}, \operatorname{hm}), \operatorname{r})))) \land ((((\operatorname{motorRun} (\operatorname{rom}, \operatorname{motorEntry} (\operatorname{w}), \operatorname{motorTime} (\operatorname{w}))).\operatorname{tape} = \operatorname{rom}) \land (((\operatorname{motorTrace} (\operatorname{rom}, \operatorname{motorEntry} (\operatorname{w}), \operatorname{motorTime} (\operatorname{w})) = \operatorname{List}.\operatorname{ofFn} ((\operatorname{fun} \operatorname{i} : \operatorname{Fin} (\operatorname{w}) \mapsto \operatorname{rom} (\operatorname{i})))) \land (\forall (\operatorname{n} : \mathbb{N}), \operatorname{motorRun} (\operatorname{rom}, \operatorname{motorEntry} (\operatorname{w}), \operatorname{motorTime} (\operatorname{w})+2*\operatorname{w}+2+\operatorname{n}) = \{\{\operatorname{motorCheckpoint} (\operatorname{rom}, \operatorname{w}, \operatorname{le}_{\operatorname{rfl}}) \operatorname{with} \operatorname{probe} := \operatorname{Fin}.\operatorname{last} (\operatorname{w})\} \operatorname{with} \operatorname{pc} := \operatorname{MotorPC}.\operatorname{halt}\}))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EncodedHead.encoded_head_copy_refinement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite ROM, the actual head-bit scan and carry execution reaches the exact macro checkpoint tape and trace, preserves all residual instruction cuts, copies the complete tape and reaches a permanent halt.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EncodedHead.encoded_head_copy_refinement`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual](../NativeFullResidual.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EventFrames](EventFrames.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode](../RarePriorResidentCode.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution](../RarePriorSerialExecution.md)
