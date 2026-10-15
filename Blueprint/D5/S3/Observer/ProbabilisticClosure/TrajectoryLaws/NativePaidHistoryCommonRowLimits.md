# Attainable stationary supports and law-preserving restriction

## Abstract

Attainable stationary supports and law-preserving restriction

Every matrix entry is M.update(op,x)(y).toReal. Ralpha and Rbeta are the ordered actual equal-pair products; the latch is the exact six-letter product. Return is the acquired beta-alpha product BA. Emissions do not weight these kernels.

**Theorem 1.1 (Positive-length Cesaro averages are stochastic).**

$$\forall Z:FiniteType, (\forall P:StochasticRealMatrixZ, (\forall w:PositiveNat, (\operatorname{CesaroStochastic}(Z, P, w))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.cesaro_stochastic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Z, real matrix P in Matrix.rowStochastic and natural w>0, cesaro(P,w) belongs to Matrix.rowStochastic. cesaro(P,w)=w^(-1) times the sum of P^a for a<w. The statement and proof are the original generic supplier.

**Theorem 1.2 (Matrix limits preserve stochasticity).**

$$\forall Z:FiniteType, (\forall P:StochasticMatrixSequenceZ, (\forall E:MatrixZ, (\forall h:TendstoPAtTopNhdsE, (\operatorname{StochasticLimit}(Z, P, E, h)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.stochastic_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite Z, matrix sequence P and matrix E, if every P(n) is row stochastic and P tends to E along atTop, then E is row stochastic. This uses entrywise nonnegativity and continuity of the finite row sums.

**Theorem 1.3 (One Cesaro subsequence for two matrices).**

$$\forall Z:FiniteType, (\forall P:StochasticRealMatrixZ, (\forall Q:StochasticRealMatrixZ, (\operatorname{PairCluster}(Z, P, Q))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.pair_cluster` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any two row-stochastic real matrices P,Q on a finite Z there exist real matrices E,F and a strictly increasing natural sequence phi with cesaro(P,phi(n)+1) tending to E and cesaro(Q,phi(n)+1) tending to F. This is the original compact matrix-pair cluster supplier.

**Theorem 1.4 (Cesaro cluster limits are fixed on both sides).**

$$\forall Z:FiniteType, (\forall P:StochasticRealMatrixZ, (\forall E:MatrixZ, (\forall w:DivergentNatSequence, (\forall h:CesaroTendstoE, (\operatorname{CesaroFixed}(Z, P, E, w, h))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.cesaro_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a row-stochastic real matrix P on finite Z, a real matrix E and a natural sequence w tending to atTop, convergence of cesaro(P,w(n)) to E implies P*E=E and E*P=E. Both equalities follow from the original telescoping residual bound. FiniteStochasticMixing consumes this with pair_cluster, stochastic_limit and cesaro_stochastic: selecting any row of the stochastic fixed E yields a normalized nonnegative stationary row.

**Theorem 1.5 (Common stochastic Cesaro limits and a rate-independent row).**

$$\forall Z:FiniteType, (\forall M:ObserverZ, (\operatorname{CommonWindowLimit}(Z, M)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_common_window_limit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CommonWindowLimit gives stochastic E,F, one strictly increasing subsequence phi, and eta=M.init.toReal*(E*F*P_S). Both equal-pair kernels fix their respective limit on the left and right. Eta is nonnegative and sums to one. For every native depth k, the literal finite double average windowAverage(M,phi(n)+1,k) tends to this same eta; every positive coordinate has an actual finite window witness. Pinned IsCompact.tendsto_subseq chooses one matrix pair. Telescoping and left stochastic contraction justify arbitrary shifts, including periodic and reducible kernels; no full mean-ergodic projection is assumed.

**Theorem 1.6 (Common reachable stationary rows with constraint transport).**

$$\forall Z:FiniteType, (\forall M:ObserverZ, (\operatorname{CommonStationaryRows}(Z, M)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_common_stationary_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CommonStationaryRows gives pi,tau,eta and the same common window subsequence before every depth quantifier. The rows are nonnegative and normalized, pi*BA=pi, pi*B=tau and tau*A=pi. Positive pi and tau labels have actual finite window-with-return witnesses. Positive B/A flows remain in the opposite positive support. A second common Cesaro cluster of BA also preserves every closed convex pair of phase constraints already satisfied by all finite-return orbits of eta. Applying this transport to the native risk region preserves every phase bound simultaneously. The bind_real identity and returned_average_actual connect real matrix products with actual PMF rows.

**Theorem 1.7 (Zero-label deletion preserves the original complete laws).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall pi:HeldPhasePRow, (\forall tau:HeldPhaseBetaRow, (\forall hX:PiHeldPhasePFibre, (\forall hY:TauHeldPhaseBetaFibre, (\forall hB:ActualReadOneSupportClosure, (\forall hA:ActualReadZeroSupportClosure, (\operatorname{NativeSupportClipping}(Z, M, e, pi, tau, hX, hY, hB, hA))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_support_clipping` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NativeSupportClipping assumes hX and hY place every positive pi and tau label on its original held phase fibre. Both hB and hA require the actual acquired read-1 and read-0 supports to lie in the opposite support. Under these hypotheses it constructs a retraction q that is the identity on retained labels and preserves project. Only zero stationary labels at the designated held active fibre are removed from transition columns; original pending, delivered and other native fields are retained. clippedObserver keeps M.init and maps acquired successors through q; clippedEmitter keeps the exact original e.emit. On positive pi and tau labels the original B and A rows are unchanged. All clipped transition support lies in retained labels. From each positive label, the clipped and original marked infinite trajectory laws, full laws and tail laws are equal. Endpoint completion updates, pending Stop, original delivery blocks and noncompletion mass are retained.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.cesaro_fixed`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.cesaro_stochastic`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_common_stationary_rows`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_common_window_limit`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.native_support_clipping`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.pair_cluster`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits.stochastic_limit`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow](NativePaidHistoryCommonRow.md)
- Dependency: [D5/S3/Observer/ProductMeasures/FinitePmfLikelihood](../../ProductMeasures/FinitePmfLikelihood.md)
