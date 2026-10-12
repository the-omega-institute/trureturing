# Fourth-segment residual laws and depth recovery

## Abstract

Original active-fourth length laws determine phase, the countable conditional depth distribution and the permitted residual transcript law.

The domain is every legal initialized finite history whose full native control is fourth active p or beta, with any installed PMF on PNat. The same latent depth governs all acquired and future Reads. Conditioning uses the actual native history cylinder. transcript(c,omega)(n) records the projected native execution at every finite event budget, including actual Read letters, active and pending controls, the matching original Stop and delivery. Past held registers are absent from this projection; their erasure is justified by the all-budget control relation, while the underlying native execution retains them.

**Theorem 1.1 (The complete stopped transcript).**

$$\forall c:AcquiredNativeState, (\forall s:ActivePhase, (\forall omega:Stream, (\forall w:\operatorname{List}(Letter), ((\operatorname{control}(c)=\operatorname{fourthActive}(s)\land \operatorname{stoppedReadWord}(s,omega)=\operatorname{some}(w))\Rightarrow(\operatorname{transcript}(c,omega)=\operatorname{reconstructTranscript}(s,\operatorname{some}(w)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.stopped_transcript` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A completed word fixes all earlier raw letters and the full native state after its original Stop. Earlier budgets agree by prefix dependence, the Stop budget agrees by the full-state stopping correspondence, and every longer budget fails after delivery. Equal controls then replace the actual full state by the canonical phase state in the projected transcript.

**Theorem 1.2 (The residual renderer on every stream).**

$$\forall c:AcquiredNativeState, (\forall s:ActivePhase, (\forall omega:Stream, ((\operatorname{control}(c)=\operatorname{fourthActive}(s))\Rightarrow(\operatorname{transcript}(c,omega)=\operatorname{reconstructTranscript}(s,\operatorname{stoppedReadWord}(s,omega))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.residual_renderer_all_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite-word case uses the stopped transcript identity. In the none case, the raw stream is the unique infinite return tail and the control relation applies at every finite budget. This pointwise identity includes noncompletion rather than conditioning it away.

**Theorem 1.3 (Transport of the actual conditional residual law).**

$$\forall mu:\operatorname{PMF}(PNat), (\forall h:\operatorname{List}(Operation), (\forall c:AcquiredNativeState, (\forall s:ActivePhase, ((\operatorname{run}(h)=\operatorname{some}(c)\land \operatorname{control}(c)=\operatorname{fourthActive}(s))\Rightarrow(\operatorname{transcriptLaw}(mu,h,c)=\operatorname{map}(\operatorname{reconstructTranscript}(s),\operatorname{wordMixture}(\operatorname{posterior}(mu,h,c),s)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.residual_law_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The countable stopped-word carrier makes its renderer measurable. The unchanged-depth conditional-tail identity gives the posterior word mixture. Composing its actual pushforward with the all-path renderer gives the residual transcript law. The original zero-mass noncompletion theorem applies at every depth and hence to arbitrary countable mixtures.

lengthProjection counts only the remaining Read letters. The two p atoms have masses sum nu(k) r(k) xi(k)^j and sum nu(k) (1-r(k))^2 xi(k)^j. The beta atoms at one, 2j+2 and 2j+3 have masses 1-mean(nu), sum nu(k) r(k)^2 xi(k)^j and sum nu(k) r(k)(1-r(k))^2 xi(k)^j, for every natural j, where xi(k)=r(k)(1-r(k)). The first atom lies in [1/3,2/5] for p and [3/5,2/3] for beta, so it separates the phases.

After phase separation, the odd p atoms or even beta atoms give all moments of eta(nu,e)=sum nu(k) r(k)^e dirac(xi(k)), with e=1 or e=2, on the compact interval [2/9,6/25]. Its total mass is at most one. The polynomial subalgebra separates this compact interval; MeasureTheory.ext_of_forall_mem_subalgebra_integral_eq_of_polish supplies finite-measure equality directly. Actual Fibonacci ratios and their xi values are injective, and positive finite singleton weights permit division to recover every posterior atom. No generic moment-determinacy claim or finite-support approximation is needed.

**Theorem 1.4 (Phase and posterior determine both laws).**

$$\forall mu:\operatorname{PMF}(PNat), (\forall rho:\operatorname{PMF}(PNat), (\forall h:\operatorname{List}(Operation), (\forall g:\operatorname{List}(Operation), (\forall c:AcquiredNativeState, (\forall d:AcquiredNativeState, (\forall s:ActivePhase, (\forall t:ActivePhase, ((\operatorname{run}(h)=\operatorname{some}(c)\land \operatorname{run}(g)=\operatorname{some}(d)\land \operatorname{control}(c)=\operatorname{fourthActive}(s)\land \operatorname{control}(d)=\operatorname{fourthActive}(t)\land s=t\land \operatorname{posterior}(mu,h,c)=\operatorname{posterior}(rho,g,d))\Rightarrow(\operatorname{lengthLaw}(mu,h,c,s)=\operatorname{lengthLaw}(rho,g,d,t)\land \operatorname{transcriptLaw}(mu,h,c)=\operatorname{transcriptLaw}(rho,g,d))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.posterior_phase_determine_both` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The posterior length mixture supplies the first equality. The residual transport identity supplies the second, using the common phase and posterior. This step concerns distributions of the same source-permitted residual object.

**Theorem 1.5 (The three original law equivalences).**

$$\forall mu:\operatorname{PMF}(PNat), (\forall rho:\operatorname{PMF}(PNat), (\forall h:\operatorname{List}(Operation), (\forall g:\operatorname{List}(Operation), (\forall c:AcquiredNativeState, (\forall d:AcquiredNativeState, (\forall s:ActivePhase, (\forall t:ActivePhase, ((\operatorname{run}(h)=\operatorname{some}(c)\land \operatorname{run}(g)=\operatorname{some}(d)\land \operatorname{control}(c)=\operatorname{fourthActive}(s)\land \operatorname{control}(d)=\operatorname{fourthActive}(t))\Rightarrow((\operatorname{lengthLaw}(mu,h,c,s)=\operatorname{lengthLaw}(rho,g,d,t)\Leftrightarrow s=t\land \operatorname{posterior}(mu,h,c)=\operatorname{posterior}(rho,g,d))\land (\operatorname{lengthLaw}(mu,h,c,s)=\operatorname{lengthLaw}(rho,g,d,t)\Leftrightarrow \operatorname{transcriptLaw}(mu,h,c)=\operatorname{transcriptLaw}(rho,g,d))\land (\operatorname{transcriptLaw}(mu,h,c)=\operatorname{transcriptLaw}(rho,g,d)\Leftrightarrow s=t\land \operatorname{posterior}(mu,h,c)=\operatorname{posterior}(rho,g,d)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.complete_original_recovery` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of length laws first gives phase and posterior equality through phase separation and compact moments. These statistics give equality of residual transcript laws. Conversely, the measurable transcriptCount selects the unique delivered budget and counts its Read operations; its actual pushforward is the length law, including none on the infinite return tail. These directions give all three displayed equivalences.

Recovered depth means its conditional distribution, not zero-error identification of this run's hidden depth or prediction of its future realization. No posterior measurement port, physical elapsed-time identity, uniform cutoff, finite mean or extra delivery of past fields follows. The result is confined to the original active fourth-segment parser and its single unpaid Stop.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.complete_original_recovery`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.posterior_phase_determine_both`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.residual_law_transport`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.residual_renderer_all_paths`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FourthSegmentLawRecovery.stopped_transcript`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeConditionalControl](NativeConditionalControl.md)
