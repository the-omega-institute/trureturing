# Attainable stationary supports and law-preserving restriction

## Abstract

Attainable stationary supports and law-preserving restriction

Every matrix entry is M.update(op,x)(y).toReal. Ralpha and Rbeta are the ordered actual equal-pair products; the latch is the exact six-letter product. Return is the acquired beta-alpha product BA. Emissions do not weight these kernels.

**Theorem 1.1 (Common stochastic Cesaro limits and a rate-independent row).**

$$\forall Z:FiniteType, (\forall M:ObserverZ, (\operatorname{CommonWindowLimit}(Z, M)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_common_window_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CommonWindowLimit gives stochastic E,F, one strictly increasing subsequence phi, and eta=M.init.toReal*(E*F*P_S). Both equal-pair kernels fix their respective limit on the left and right. Eta is nonnegative and sums to one. For every native depth k, the literal finite double average windowAverage(M,phi(n)+1,k) tends to this same eta; every positive coordinate has an actual finite window witness. Pinned IsCompact.tendsto_subseq chooses one matrix pair. Telescoping and left stochastic contraction justify arbitrary shifts, including periodic and reducible kernels; no full mean-ergodic projection is assumed.

**Theorem 1.2 (Common reachable stationary rows with constraint transport).**

$$\forall Z:FiniteType, (\forall M:ObserverZ, (\operatorname{CommonStationaryRows}(Z, M)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_common_stationary_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CommonStationaryRows gives pi,tau,eta and the same common window subsequence before every depth quantifier. The rows are nonnegative and normalized, pi*BA=pi, pi*B=tau and tau*A=pi. Positive pi and tau labels have actual finite window-with-return witnesses. Positive B/A flows remain in the opposite positive support. A second common Cesaro cluster of BA also preserves every closed convex pair of phase constraints already satisfied by all finite-return orbits of eta. Applying this transport to the native risk region preserves every phase bound simultaneously. The bind_real identity and returned_average_actual connect real matrix products with actual PMF rows.

**Theorem 1.3 (Zero-label deletion preserves the original complete laws).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall pi:HeldPhasePRow, (\forall tau:HeldPhaseBetaRow, (\forall hX:PiHeldPhasePFibre, (\forall hY:TauHeldPhaseBetaFibre, (\forall hB:ActualReadOneSupportClosure, (\forall hA:ActualReadZeroSupportClosure, (\operatorname{NativeSupportClipping}(Z, M, e, pi, tau, hX, hY, hB, hA))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_support_clipping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NativeSupportClipping assumes hX and hY place every positive pi and tau label on its original held phase fibre. Both hB and hA require the actual acquired read-1 and read-0 supports to lie in the opposite support. Under these hypotheses it constructs a retraction q that is the identity on retained labels and preserves project. Only zero stationary labels at the designated held active fibre are removed from transition columns; original pending, delivered and other native fields are retained. clippedObserver keeps M.init and maps acquired successors through q; clippedEmitter keeps the exact original e.emit. On positive pi and tau labels the original B and A rows are unchanged. All clipped transition support lies in retained labels. From each positive label, the clipped and original marked infinite trajectory laws, full laws and tail laws are equal. Endpoint completion updates, pending Stop, original delivery blocks and noncompletion mass are retained.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_common_stationary_rows`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_common_window_limit`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_support_clipping`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow](NativePaidHistoryCommonRow.md)
- Dependency: [D5/S3/Observer/ProductMeasures/FinitePmfLikelihood](../../ProductMeasures/FinitePmfLikelihood.md)
