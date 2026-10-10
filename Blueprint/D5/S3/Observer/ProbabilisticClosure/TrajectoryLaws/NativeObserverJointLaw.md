# The constructed actual law

## Abstract

Ordered acquired observer rows and the same-source full history law.

Every statement is universal in a type Z with Fintype, MeasurableSpace and MeasurableSingletonClass, an Observer M on Z and an arbitrary probability mass function mu on positive integer Depth. Z is the one finite COMPLETE carrier. M.project reads the original FiniteFields; initialization has support over the original initial fields. M.update(op,z) is a fixed source-independent PMF on Z. Each supported successor projects to finiteStep when that original operation is lawful. There is no depth, history, posterior, readable distribution, clock or paid counter argument in M. Numerical representation, selectors, workspace and all persistent random state must belong to this finite carrier in any implementation mapped to the interface.

advance applies the acquired kernels by recursive PMF.bind in the actual operation order, and row(M,h)=advance(M,M.init,h). Equal letter counts determine source likelihoods, not these ordered products. cutHistory reads the successful native operation prefix at an event cut and saturates after delivered Stop. privateKernel(M,n)(k,omega) is the measure of row(M,cutHistory(omega,n)). actualLaw is jointLaw(mu) composed with this explicitly constructed Markov kernel. This is a probability measure, not an arbitrary joint-law field. The source draws one K and supplies every seed and payload Read conditional independently at rate(K). Analysis histories, counts and rows are not runtime data.

ListOperation means List Operation, SetStream means Set Stream, and fields(c)=c.source.finiteFields. mass(L,A,{z}) is L(A times {z}); mass(L,E) is L(E). historyCut(h,c)=nativeEvent(h,c) times the whole Z carrier. taggedHistory(h,c,k,E) is the intersection of nativeEvent(h,c) with the set of (K,omega) satisfying K=k and rawTail(omega,length(readLetters(h))) in E. Deterministic original events add no likelihood. Every legal h has a positive normalizer under every installed PMF; neither paid rejections, partial parses nor fourth returns are excluded.

**Theorem 1.1 (Full ordered history factorization).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall mu:PMFDepth, (\forall h:ListOperation, (\forall c:AcquiredNativeState, ((\operatorname{run}(h)=\operatorname{some}(c))\Rightarrow(\forall k:Depth, (\forall z:Z, (\forall E:SetStream, ((\operatorname{MeasurableSet}(E))\Rightarrow(\operatorname{mass}(\operatorname{actualLaw}(M,mu,\operatorname{length}(h)),\operatorname{taggedHistory}(h,c,k,E),\operatorname{singleton}(z))=\operatorname{at}(mu,k)\cdot\operatorname{likelihood}(h,k)\cdot\operatorname{at}(\operatorname{row}(M,h),z)\cdot\operatorname{mass}(\operatorname{rawReadLaw}(\operatorname{rate}(k)),E))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.ordered_history_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original legal history, every source depth, every configuration and every measurable unread-source event, the joint mass factors as mu(k) times its original acquired-word likelihood times the ordered private row times the same-depth unread-source law. The kernel is constant on the exact native history cylinder. Prefix-tail independence is used at that same depth. No future-event condition or reset is introduced.

**Theorem 1.2 (Conditional source and private row).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall mu:PMFDepth, (\forall h:ListOperation, (\forall c:AcquiredNativeState, ((\operatorname{run}(h)=\operatorname{some}(c))\Rightarrow(\operatorname{cond}(\operatorname{actualLaw}(M,mu,\operatorname{length}(h)),\operatorname{historyCut}(h,c))=\operatorname{prod}(\operatorname{cond}(\operatorname{jointLaw}(mu),\operatorname{nativeEvent}(h,c)),\operatorname{toMeasure}(\operatorname{row}(M,h))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.conditional_history_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

After conditioning on the full native history, the joint source/private measure is the product of the conditional original source measure and the entire ordered row. All configurations remain in the conditional law, including rows that can occur only at earlier transient histories.

**Theorem 1.3 (Retain K while deleting acquired Reads).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall mu:PMFDepth, (\forall h:ListOperation, (\forall c:AcquiredNativeState, ((\operatorname{run}(h)=\operatorname{some}(c))\Rightarrow(\operatorname{map}(\operatorname{cond}(\operatorname{actualLaw}(M,mu,\operatorname{length}(h)),\operatorname{historyCut}(h,c)),\operatorname{sameKShift}(h))=\operatorname{prod}(\operatorname{jointLaw}(\operatorname{posterior}(mu,h,c)),\operatorname{toMeasure}(\operatorname{row}(M,h))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.sameK_private_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

sameKShift(h) maps ((k,omega),z) to ((k,rawTail(omega,length(readLetters(h)))),z). The unread source is jointLaw of the original posterior and the private row is unchanged. K is retained literally. This supplier is used in the full target transport proof.

**Theorem 1.4 (Full native state at every acquired row).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall h:ListOperation, (\forall c:AcquiredNativeState, ((\operatorname{run}(h)=\operatorname{some}(c))\Rightarrow((\forall z:Z, ((\operatorname{inSupport}(z,\operatorname{row}(M,h)))\Rightarrow(\operatorname{project}(M,z)=\operatorname{fields}(c))))\land((\forall op:Operation, (\operatorname{row}(M,\operatorname{append}(h,\operatorname{singletonList}(op)))=\operatorname{bind}(\operatorname{row}(M,h),\operatorname{update}(M,op))))\land(\exists nf:PrefixForm, ((\operatorname{render}(nf)=h)\land((c=\operatorname{reconstruct}(nf))\land(\operatorname{PrefixFacts}(nf,c))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.actual_row_refines` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every positive row configuration has the actual native fields. Appending any operation composes the same acquired update even if a separate synthetic emission gives it zero probability. A legal history also has its original PrefixForm witness, with full reconstruction and PrefixFacts. Both seeds, every accepted or rejected paid pair, all marker branches and unbounded return counts remain covered by this original grammar.

validStopped(s,omega) pairs stoppedReadWord with its WordFamily witness, or with the unique infinite noncompletion outcome. rawTarget(mu,h,c,s) is the conditional original source mapped to validStopped on its unread tail. fullTarget(M,mu,h,c) is the conditional actual source/private law mapped to the full native transcript of that same tail. The valid carrier retains old synthetic noncompletion; the actual posterior mixture has the original homogeneous stopped-word masses. No clipped law is constructed here.

PhaseHistory(s) consists of every pair H=(h,c) with run(h)=some(c) and c in fourth active phase s. It has no length or rejection bound. LawfulDecoderFamily means a function D assigning to each such H and configuration z a measure on ValidTail(s); it is a separately supplied decoded law, not a constructed generator. fullRisk is the supremum over this entire history type of the finite sum row(M,h)(z) times TV of the rendered D(H,z) and fullTarget. rawRisk uses D(H,z) and rawTarget in the same order. TV is the canonical ENNReal event-supremum measurableTotalVariation. In particular the averaging occurs after TV, before the history supremum.

CutEvidence(M,mu,s,H), for H=(h,c), is the conjunction of: rawTarget and fullTarget are probability measures; fullTarget=(fullRenderer(c,s))_*rawTarget; (Subtype.val)_*rawTarget=wordMixture(posterior(mu,h,c),s); the conditional actual private marginal equals row(M,h).toMeasure; the positive configuration projection; the ordered append-update equality; and the PrefixForm reconstruction in actual_row_refines. It includes the full ordered tagged-history mass factorization for every k, z and measurable unread E, with the same formula as ordered_history_factorization at H. It also includes both full event obligations: for every raw omega and lawful nextNative(c,omega)=(op,d), deleting one operation and its whole event block from fullTranscript(c,omega) equals fullTranscript(d,rawTail(omega,readCost(op))); and for every omega in the acquired readLetters(h) cylinder, the initial full transcript at length(h) contains h, fields(c) and all original blocks, whose replay reconstructs fields(c) and originalView(c). These are all original theorem conjuncts, not additional assumptions.

**Theorem 1.5 (Actual full target and all-history risk transport).**

$$\forall Z:Type, ((\operatorname{FiniteMeasurableSingleton}(Z))\Rightarrow(\forall M:ObserverZ, (\forall mu:PMFDepth, (\forall s:ActivePhase, (\forall D:LawfulDecoderFamily, ((\forall H:PhaseHistory, (\operatorname{CutEvidence}(M,mu,s,H)))\land(\operatorname{fullRisk}(M,mu,s,D)=\operatorname{rawRisk}(M,mu,s,D))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.native_history_risk_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The full target is proved equal to the rendered constructed raw target, with its posterior stopped-word mixture. The entire actual conditional row and original event reconstruction are transported. Two measurable inverses preserve each configuration distance, so the original full-history supremum equals the raw supremum. The original source likelihood uses all acquired Reads. The law, row and field clauses are live consumers of the renderer, same-K and native reconstruction results.

This bridge concerns the exact native source and source-independent finite acquired updates. It does not construct an arbitrary observer's synthetic decoded generator or establish its exact generation equation, a counted realization theorem, common stationary actual rows, endpoint concentration, normalized clipped laws or clipping distortion. Those connections remain required before applying the regular-table separator to the original observer lower bound. No conclusion of the strict 1/195200 bound is asserted here.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.actual_row_refines`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.conditional_history_product`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.native_history_risk_transport`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.ordered_history_factorization`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.sameK_private_tail`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual](NativeFullResidual.md)
