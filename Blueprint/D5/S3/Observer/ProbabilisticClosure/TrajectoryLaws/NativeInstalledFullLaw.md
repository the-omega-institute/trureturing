# The installed generator and its complete trajectory

## Abstract

Installed configuration laws with literal native event blocks.

Z is the original finite COMPLETE configuration carrier, with Fintype, MeasurableSpace and MeasurableSingletonClass. Observer M is unchanged: project reads the original FiniteFields and update(op,z) is its original source-independent probability row. init is used for actual acquired histories; it is never resampled in a synthetic residual law. InstalledEmitter e adds a semantic PMF emit(z) on Option Operation. Its supported some(op) must be lawful under finiteStep(project(z),op), and supported none requires delivered control. Hence seed, early and fourth active states emit Reads, pending(b) emits its matching Stop surely, and delivered emits none surely. The law may depend on every component of Z. These are semantics of a charged installed program, without an executable realization assertion for arbitrary real probability tables.

MarkedPathZ means a stream of pairs in W=Z times Option Operation. W is an analysis carrier, not additional COMPLETE memory. markedRow(M,e,(z,a)) samples emit(z), then for some(op) samples exactly M.update(op,z) and records (zprime,some(op)). For none it preserves z and records (z,none). markedKernel is this PMF as a Markov kernel. markedLaw starts from the delta at (z,none) and uses Mathlib Kernel.trajMeasure; its first-edge decomposition is a measure equality on the entire infinite trajectory. The frozen MarkovPrefixMass singleton-prefix formula identifies its finite-dimensional measures, and projective uniqueness extends the decomposition to all measurable path events. No conditional row or division by an emission probability is used.

operations(x,n) collects incoming marks at coordinates 1 through n; coordinate 0 is ignored. Its value is none after the first padding mark. markedTranscript(M,x)(n) records these operation prefixes, M.project(x(n).first), and eventBlocks generated from the initial projected fields. rawFrom(x)(i) reads the Read letter from the incoming mark at i+1, using a dummy alpha for Stop or padding. On a coherent trajectory all Reads precede Stop, so the dummy letters occur only where the native delivered parser cannot read them. representative(f) supplies the fields f with zero analysis counts and zero payloadReturns. Those counters do not enter the full output.

Coherent(M,x) means that every Edge(M,x(n),x(n+1)) holds. A some(op) edge projects to exactly finiteStep; a none edge starts at delivered and preserves the same private configuration. AlmostSureNative(M,e,z) means that for almost every x under markedLaw(M,e,(z,none)), markedTranscript(M,x)=fullTranscript(representative(project(M,z)),rawFrom(x)). The PMF support of every trajectory edge gives coherence simultaneously for all natural event indices. Full native execution retains paid seed rejection, both accepted seeds, every marker triple, arbitrary payload returns, current registers and the Stop transaction. The completion event list writes before latching and preserves the complete held records.

**Theorem 1.1 (The entire marked trajectory regenerates after one edge).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall w:MarkedZ, (\operatorname{markedLaw}(M, e, w)=\operatorname{weightedPrependedLaws}(M, e, w))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.marked_regenerate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every initial marked state w, weightedPrependedLaws(M,e,w) is the sum over all v in Marked(Z) of markedRow(M,e,w)(v) times the image of markedLaw(M,e,v) under x mapped to prepend(w,x). prepend(w,x)(0)=w and prepend(w,x)(n+1)=x(n). The equality is on the entire marked path space, without conditioning or a positive-edge assumption.

**Theorem 1.2 (The initial marked state is retained almost surely).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall w:MarkedZ, (\operatorname{AlmostEveryMarkedHead}(M, e, w))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.marked_head` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

AlmostEveryMarkedHead(M,e,w) means that x(0)=w for almost every x under markedLaw(M,e,w). The statement quantifies over every finite measurable singleton COMPLETE carrier, its original observer, each lawful installed emitter and every marked initial state, including incoming Stop and padding marks.

**Theorem 1.3 (The marked decoder is the original native execution).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall x:MarkedPathZ, ((\operatorname{Coherent}(M, x))\Rightarrow(\forall c:AcquiredNativeState, ((\operatorname{fields}(c)=\operatorname{projectAtZero}(M, x))\Rightarrow(\operatorname{markedTranscript}(M, x)=\operatorname{fullTranscript}(c, \operatorname{rawFrom}(x)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.marked_native_realization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every coherent infinite marked trajectory and every acquired native state with the same initial finite fields, the two full transcripts coincide at every cut. The construction follows the incoming Read letters and the projected actual update edges. A matching Stop performs its native update and entire event block; the following padding produces none. No eventual completion, irreducibility or positivity of each transition is assumed.

fullLaw(M,e,z) is the pushforward of markedLaw(M,e,(z,none)) by markedTranscript(M). It is a normalized probability measure on FullTranscript. It has no history, prior, posterior, latent depth or clock argument. Infinite noncompletion is part of this probability space. In particular distinct infinite seed-rejection streams retain their different operation prefixes; none is not a global compression of seed noncompletion. Equality for native states with identical finite fields uses drive_control, drive_spec and the original execute_finite_projection. These deterministic results identify finite fields and event blocks without imposing constraints on the analysis counters.

For an active fourth phase s, tailValue(s,omega) is stoppedReadWord(s,omega) with its WordFamily validity proof. tailLaw(M,e,s,z) is its pushforward from the same marked trajectory via rawFrom. ValidTail(s) contains the legal finite fourth words and their unique infinite noncompletion word. This fourth-only none outcome does not collapse the complete seed parser. Both fullLaw and tailLaw are probability measures even at emission endpoints and when fourth noncompletion has mass one. For scalar return data A=B=1,u=0,v=1, the infinite trajectory is retained; no resolvent or eventual-completion hypothesis enters.

**Theorem 1.4 (A configuration law renders the full fourth future).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall s:ActivePhase, (\forall z:Z, (\forall c:AcquiredNativeState, (((\operatorname{project}(M, z)=\operatorname{fields}(c))\land(\operatorname{control}(\operatorname{fields}(c))=\operatorname{fourthActive}(s)))\Rightarrow(\operatorname{fullLaw}(M, e, z)=\operatorname{map}(\operatorname{tailLaw}(M, e, s, z), \operatorname{fullRenderer}(c, s))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.installed_configuration_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Whenever project(M,z)=c.source.finiteFields and c is fourth-active(s), fullLaw(M,e,z) is the image of tailLaw(M,e,s,z) under fullRenderer(c,s). The same z determines the complete law on both sides. The identity follows from actual marked realization, deterministic finite-fields factorization and full_renderer_all_paths. It preserves every original operation, finite held field and literal event block.

blockEvent(f,fprime,op,E) is the measurable set of transcripts t satisfying t(0)=some([],f,[]), t(1)=some([op],fprime,[eventBlock(f,op)]), and deleteBlock(t) in E. DeleteBlock removes one operation and its entire original block. weightedSuccessorMass(M,e,z,op,E) denotes the finite sum over zprime in Z of M.update(op,z)(zprime) times fullLaw(M,e,zprime)(E). emissionMass(e,z,some(op)) is e.emit(z)(some(op)). These rows are bound before synthesis and remain the literal original rows at zero emission.

**Theorem 1.5 (Exact first-block recursion).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall z:Z, (\forall op:Operation, (\forall fprime:FiniteFields, ((\operatorname{finiteStep}(\operatorname{project}(M, z), op)=\operatorname{some}(fprime))\Rightarrow(\forall E:SetFullTranscript, ((\operatorname{MeasurableSet}(E))\Rightarrow(\operatorname{mass}(\operatorname{fullLaw}(M, e, z), \operatorname{blockEvent}(\operatorname{project}(M, z), fprime, op, E))=\operatorname{emissionMass}(e, z, \operatorname{some}(op))\cdot\operatorname{weightedSuccessorMass}(M, e, z, op, E)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.installed_first_block_recursion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every lawful finiteStep and every measurable full residual event, the block-event mass equals the emission mass times the original-update average of successor full laws. The unconditional trajectory decomposition is applied before decoding; the first native block and its entire deleted suffix are identified on supported paths. This proves the equation for arbitrary measurable E, including noncompletion events, without a positivity premise on the emission.

terminalTranscript(f) has coordinate 0 equal to some([],f,[]) and every later coordinate none. pending(b) and delivered in the formulas mean the corresponding fourth controls. installedRisk(M,e,mu,s) is the supremum over every PhaseHistory(s) of the actual row-weighted measurable total variation between fullLaw(M,e,z) and fullTarget(M,mu,h,c). HistoryIndependentTailLaw denotes the family (H,z) mapped to tailLaw(M,e,s,z); AlmostSureNative is the path equality defined above. PMFDepth includes all finite or countable positive-integer priors. The source keeps one common latent K; no endpoint mass assumption is needed for this transport identity.

**Theorem 1.6 (One installed law supplies generation and history risk transport).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall e:InstalledEmitterM, ((\forall z:Z, (\operatorname{IsProbabilityMeasure}(\operatorname{fullLaw}(M, e, z))))\land((\forall z:Z, (\operatorname{AlmostSureNative}(M, e, z)))\land((\forall z:Z, (\forall op:Operation, (\forall fprime:FiniteFields, ((\operatorname{finiteStep}(\operatorname{project}(M, z), op)=\operatorname{some}(fprime))\Rightarrow(\forall E:SetFullTranscript, ((\operatorname{MeasurableSet}(E))\Rightarrow(\operatorname{mass}(\operatorname{fullLaw}(M, e, z), \operatorname{blockEvent}(\operatorname{project}(M, z), fprime, op, E))=\operatorname{emissionMass}(e, z, \operatorname{some}(op))\cdot\operatorname{weightedSuccessorMass}(M, e, z, op, E))))))))\land((\forall z:Z, (\forall b:Letter, ((\operatorname{control}(\operatorname{project}(M, z))=\operatorname{pending}(b))\Rightarrow(\operatorname{emit}(e, z)=\operatorname{pure}(\operatorname{some}(\operatorname{stop}(b)))))))\land((\forall z:Z, ((\operatorname{control}(\operatorname{project}(M, z))=\operatorname{delivered}())\Rightarrow(\operatorname{fullLaw}(M, e, z)=\operatorname{dirac}(\operatorname{terminalTranscript}(\operatorname{project}(M, z))))))\land(\forall mu:PMFDepth, (\forall s:ActivePhase, (\operatorname{installedRisk}(M, e, mu, s)=\operatorname{rawRisk}(M, mu, s, \operatorname{HistoryIndependentTailLaw}(M, e, s)))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.installed_full_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The six conjuncts give full-law normalization, almost-sure literal native realization, exact arbitrary-event recursion, forced pending Stop emission, the delivered Dirac law, and equality of installed configuration-before-TV risk with rawRisk for the history-independent tail family. The risk proof uses actual_row_refines at every original PhaseHistory and native_history_risk_transport. Zero-weight configurations contribute zero; supported configurations satisfy the full renderer identity. This includes all positive finite paid seed histories and all fourth returns, rather than only the first fourth p cut.

Definitions 1.1 and 1.2 supply the same-depth source, complete original fields and literal event renderer. Definition 1.3 supplies the finite COMPLETE carrier and its installed semantic emissions and source-independent updates; the first-block theorem gives its exact generation equation for the constructed D laws. The configuration identity makes the tail family history-independent and applies the existing full-history risk transport to those constructed laws. Definition 1.4 still requires the designated seed-1, marker-100 fibre and constant suspended alpha emission there; it asserts no equality of suspended laws or update rows.

The original strict bound e(M)>1/195200 is not a conclusion of these statements. Its remaining connections are bounded ENNReal-to-real risk and excess conversion, extraction of common actual stationary rows for countable priors, normalized clipping with its distortion bound, and application of ConstantSuspensionSeparator on the resulting regular table. The constant-emission condition must be transported on the designated reachable fibre. No unrestricted-observer gap or free exact-real sampling assertion follows.

**Theorem 1.7 (Prepending a marked head is measurable).**

$$\forall A:MeasurableType, (\forall a:A, (\operatorname{MeasurablePrepend}(a)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.measurable_prepend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every measurable carrier A and a in A, prepend(a) on infinite A paths is measurable. Its zero coordinate is constant and each successor coordinate is the corresponding original path coordinate.

**Theorem 1.8 (The marked read projection is measurable).**

$$\forall Z:FiniteMeasurableSingletonType, (\operatorname{RawFromMeasurable}(Z))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.rawFrom_measurable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The map rawFrom from infinite marked Z paths to binary streams is measurable on the original finite measurable singleton carrier. Coordinate n reads the incoming mark at n+1 and uses zero for marks that are not Reads.

**Theorem 1.9 (The marked acquired operation uses the original kernel).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall z:Z, (\forall zprime:Z, (\forall op:Operation, (\operatorname{MarkedSomeMass}(M, e, z, zprime, op))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.marked_some_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original configurations z,zprime and operation op, markedRow(M,e,(z,none),(zprime,some(op))) equals e.emit(z)(some(op)) times M.update(op,z)(zprime). The original update is used even when the emission has zero mass.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.installed_configuration_identity`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.installed_first_block_recursion`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.installed_full_law`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.marked_head`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.marked_native_realization`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.marked_regenerate`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.marked_some_mass`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.measurable_prepend`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw.rawFrom_measurable`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkovPrefixMass](MarkovPrefixMass.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw](NativeObserverJointLaw.md)
