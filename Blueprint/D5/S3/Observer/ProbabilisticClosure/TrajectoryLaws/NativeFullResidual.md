# Native full event space

## Abstract

Full original residual rendering and event deletion.

FiniteFields and its original writers come from NativeAcquiredPrefixState. Its control is the paid seed parser, early segment count and phase, fourth active phase, matching pending Stop or delivered Stop. Registers retain seed, live weight and syndrome, both ordered Q-plus records, first-marker Z and the held third snapshot. The snapshot stores seed, weight and syndrome; its ell and completed count are the fixed values 2 and 3. originalView supplies these constants, the fixed four-slot selector, the selected markers recovered from the written registers, marker-written and latch flags, and the exact partial finiteStep permission menu. No paid count, return counter, posterior or archive enters the rendered fields.

OriginalEvent is generated from the old fields. Every Read is retained. Seed pairs either reject and return to ready, or acquire their first letter as the seed. Payload p completes zero on alpha and suspends on beta; suspension returns on alpha and completes one on beta. A completion records its index and bit, writes live arithmetic and the original ordinal records, then performs the third latch when its old index is two. beforeLatch restores the old snapshot in the post-write event; only latched installs the new snapshot. The fourth write changes live arithmetic while Q-plus, Z and snapshot hold. Matching Stop records its bit and enters delivered. Illegal operations have no native successor.

FullTranscript is a measurable sequence of prefix cuts. A successful cut contains its complete operation prefix, full native finite fields and the ordered list of whole original event blocks. Initial fields are retained at cut zero. FullOutput has the discrete measurable structure; FullTranscript has the product structure. ListOperation means List Operation; tuple and at denote the displayed product and evaluation. fields(c) means c.source.finiteFields. replayBlock folds the individual written, latched, moved and held events over the old finite fields. originalView is determined by those fields, rather than an additional observer state.

**Theorem 1.1 (Lawful event reconstruction).**

$$\forall c:AcquiredNativeState, (\forall d:AcquiredNativeState, (\forall omega:Stream, (\forall n:Nat, (\forall k:Nat, (\forall ops:ListOperation, ((\operatorname{nativeDrive}(c,omega,n)=\operatorname{some}(\operatorname{tuple}(ops,d,k)))\Rightarrow((\operatorname{at}(\operatorname{fullTranscript}(c,omega),n)=\operatorname{some}(\operatorname{tuple}(ops,\operatorname{fields}(d),\operatorname{eventBlocks}(\operatorname{fields}(c),ops))))\land((\operatorname{foldl}(replayBlock,\operatorname{fields}(c),\operatorname{eventBlocks}(\operatorname{fields}(c),ops))=\operatorname{fields}(d))\land(\operatorname{originalView}(\operatorname{foldl}(replayBlock,\operatorname{fields}(c),\operatorname{eventBlocks}(\operatorname{fields}(c),ops)))=\operatorname{originalView}(\operatorname{fields}(d)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.full_event_reconstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every successful native prefix, replay of all actual event blocks reconstructs its fields and the original field view, including permissions. Induction over the executed operations uses the literal seed, payload and Stop cases. This statement applies to every initial native state and every lawful stream prefix, with no bound on paid returns.

**Theorem 1.2 (Delete one complete original block).**

$$\forall c:AcquiredNativeState, (\forall d:AcquiredNativeState, (\forall omega:Stream, (\forall op:Operation, ((\operatorname{nextNative}(c,omega)=\operatorname{some}(\operatorname{tuple}(op,d)))\Rightarrow(\operatorname{deleteBlock}(\operatorname{fullTranscript}(c,omega))=\operatorname{fullTranscript}(d,\operatorname{rawTail}(omega,\operatorname{readCost}(op))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.full_delete_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

deleteBlock shifts the prefix index by one, deletes the first operation and deletes the first whole event block. It retains the successor fields. Read shifts the source by one; Stop has readCost zero. Native resumption and finite projection prove equality with the successor transcript. No operation is removed without its deterministic block.

ValidTail(s) is the subtype of RawTail whose finite elements are precisely some w with a WordFamily(s,b,w) witness for a bit b. It also contains none, representing the unique infinite noncompletion word. tailStream uses wordStream on finite words and infiniteTail on none. Thus the carrier retains every legal finite completion word and the old synthetic noncompletion possibility. At suspension, the already acquired beta is absent from future Reads.

**Theorem 1.3 (Every raw path has its full representative).**

$$\forall c:AcquiredNativeState, (\forall s:ActivePhase, (\forall omega:Stream, ((\operatorname{control}(\operatorname{fields}(c))=\operatorname{fourthActive}(s))\Rightarrow(\operatorname{fullTranscript}(c,omega)=\operatorname{fullTranscript}(c,\operatorname{tailStream}(s,\operatorname{stoppedReadWord}(s,omega)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.full_renderer_all_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For active native fourth control, every source stream renders identically to its stopped word representative. The noncompletion case is the unique infinite word, with all its prefix fields and blocks. The finite case agrees at every acquired prefix, its completion, matching Stop and every later failed cut.

**Theorem 1.4 (Full rendering has measurable readback).**

$$\forall c:AcquiredNativeState, (\forall s:ActivePhase, ((\operatorname{control}(\operatorname{fields}(c))=\operatorname{fourthActive}(s))\Rightarrow(\forall t:RawTail, ((\operatorname{Valid}(s,t))\Rightarrow(\operatorname{readbackRaw}(\operatorname{fullRenderer}(c,s,\operatorname{validPair}(t)))=t)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.full_renderer_readback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

validPair(t) is t with its Valid proof. readbackRaw locates the unique delivered cut and reads back every Read letter there; if none exists it returns none. The delivered cut index is measurable by measurable first occurrence. The proof recovers exactly t on the lawful carrier. The auxiliary control projection is used only to locate delivery; it is not the rendered full law.

**Theorem 1.5 (Exact full-law total variation transport).**

$$\forall c:AcquiredNativeState, (\forall s:ActivePhase, (\forall P:MeasureValidTail, (\forall Q:MeasureValidTail, ((\operatorname{control}(\operatorname{fields}(c))=\operatorname{fourthActive}(s))\Rightarrow(\operatorname{TV}(\operatorname{map}(P,\operatorname{fullRenderer}(c,s)),\operatorname{map}(Q,\operatorname{fullRenderer}(c,s)))=\operatorname{TV}(P,Q))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.full_renderer_tv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

MeasureValidTail means Measure (ValidTail s). TV is canonical measurableTotalVariation, the ENNReal supremum of the two directed event gaps. Measurable rendering and its measurable left inverse give equality by the two map contractions. The statement holds for arbitrary measures on the lawful carrier, including measures with noncompletion mass. No half-l1 or real-valued convention is substituted.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.full_delete_block`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.full_event_reconstruction`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.full_renderer_all_paths`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.full_renderer_readback`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.full_renderer_tv`
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction](../../../Estimation/DataProcessing/MeasurablePostprocessingDefectContraction.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery](FourthSegmentLawRecovery.md)
