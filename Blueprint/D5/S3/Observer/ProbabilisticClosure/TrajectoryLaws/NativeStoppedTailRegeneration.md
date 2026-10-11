# Complete native stopped laws

## Abstract

NativeStoppedTailRegeneration

**Theorem 1.1 (First completion under one prefixed read).**

$$\forall omega:BinaryStream, (\operatorname{StoppedReadCons}(omega))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration.stopped_read_cons` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stream is an arbitrary infinite binary stream. At p a leading zero completes with word [0], and at beta a leading one completes with word [1]. A leading one at p prefixes one to the beta stopped tail, while a leading zero at beta prefixes zero to the p stopped tail. Option.map sends none to none. The finite-word fibre theorem and the native parser establish both finite stopping shifts; exhaustiveness of Option then retains the infinite noncompletion case.

**Theorem 1.2 (Complete native two-phase generation).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\operatorname{NativeStoppedTailRegeneration}(Z, M, e))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration.native_stopped_tail_regeneration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Z is the original finite COMPLETE carrier with its measurable singleton structure, M is the source-independent original observer and e is any lawful installed emitter. rawTailLaw is tailLaw pushed through Subtype.val, and remains a probability law. For each z whose projected control is fourth(active p), and every set E of raw tails, Q(z,E) equals u(z) times the indicator of some[0] in E plus (1-u(z)) times the sum over zprime of M.update(read1,z,zprime).toReal times W(zprime,prefix1 inverse E). For fourth(active beta) the corresponding equation is (1-v(z)) times the indicator of some[1] in E plus v(z) times the sum of M.update(read0,z,zprime).toReal times Q(zprime,prefix0 inverse E). Both u and v are the original read0 emission probability at the respective configuration. Each equation requires the actual current-control hypothesis; normalization alone does not provide it. The marked regeneration identity, incoming-mark invariance and almost-sure initial-head identity establish the pushforward law. All events, including none, are retained. Completing reads keep the matching pending Stop and its original update and full renderer.

**Theorem 1.3 (Raw projection preserves total variation).**

$$\forall s:ActivePhase, (\forall P:MeasureValidTailS, (\forall Q:MeasureValidTailS, (\operatorname{RawProjectionTV}(s, P, Q))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration.raw_projection_tv` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every active phase s and arbitrary measures P and Q on ValidTail s, total variation of their Subtype.val pushforwards equals total variation of P and Q. The measurable retraction sends invalid words to valid none and is a left inverse on every valid tail. Probability or original termination is not required.

**Theorem 1.4 (The endpoint source laws on raw tails).**

$$\forall k:PositiveDepth, (\forall s:ActivePhase, (\operatorname{PureRawLaw}(k, s)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration.pure_raw_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive depth k and active phase s, pureTail(k,s) pushed through Subtype.val equals explicitStoppedWordLaw(s,rate(k)). This is a direct application of the original stopped-word pushforward theorem. In particular depths one and two have rates 1/3 and 2/5.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration.native_stopped_tail_regeneration`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration.pure_raw_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration.raw_projection_tv`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeStoppedTailRegeneration.stopped_read_cons`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw](NativeInstalledFullLaw.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow](NativePaidHistoryCommonRow.md)
