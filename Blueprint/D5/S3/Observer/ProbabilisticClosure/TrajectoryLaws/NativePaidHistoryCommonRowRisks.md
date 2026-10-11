# Full common stationary risk implication

## Abstract

Full common stationary risk implication

Configuration-before-TV and law-before-TV retain separate original installedRisk and installedLawRisk right-hand sides. Both are the unrestricted original legal PhaseHistory suprema. Every approximant uses its own posterior target before averaging.

**Theorem 1.1 (Original risk constraints on every fixed return of the common limit).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall mu:PMFDepth, (\forall eta:CommonWindowLimitRow, (\forall phi:CommonWindowSubsequence, (\operatorname{NativeOrbitRisks}(Z, M, e, mu, eta, phi)))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowRisks.native_orbit_original_risks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NativeOrbitRisks says eta*(BA)^j and eta*(BA)^j*B belong to their phase risk regions for every j. A region imposes configurationCost<=installedRisk.toReal and both directed measurable-event gaps<=installedLawRisk.toReal for every supported depth of mu. Original target-TV convergence, the frozen measurable TV triangle and actual-history bounds supply uniform finite-window errors. The real row averages are affine functionals of genuine histories; their limits preserve the original bounds. The countable complete law is handled event by event, without assuming continuity of a finite outcome approximation.

**Theorem 1.2 (One PMF pair satisfies all four original bounds).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall mu:PMFDepth, (\operatorname{CommonFourRisks}(Z, M, e, mu)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowRisks.native_common_stationary_four_risks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

CommonFourRisks gives one pi,tau:PMF Z with pi.bind(M.update(read1))=tau and tau.bind(M.update(read0))=pi. Every positive label has a finite native paid-history witness and both actual acquired supports are closed. For every supported k, sum(pi_x*TV(tailLaw_p(x),pureTail(k,p)))<=installedRisk_p, sum(tau_y*TV(tailLaw_beta(y),pureTail(k,beta)))<=installedRisk_beta, TV(tailMixture_p(pi),pureTail(k,p))<=installedLawRisk_p and TV(tailMixture_beta(tau),pureTail(k,beta))<=installedLawRisk_beta. The closed convex intersection includes all supported depths simultaneously. There is no per-depth optimizer or subsequence.

**Theorem 1.3 (Full native common stationary-row implication).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall mu:PMFDepth, (\operatorname{NativeCompleteCommonRows}(Z, M, e, mu)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowRisks.native_complete_common_rows` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NativeCompleteCommonRows has one pair pi,tau before forall supported k and both phases. It contains the original bind stationarity equations, all four configuration/law inequalities, actual positive finite window-with-return witnesses with positive original normalizers, the exact seed-1 marker-100 held fields and each label's installed_configuration_identity. It also constructs the support retraction and preserves the complete generated infinite path laws while leaving positive acquired B/A rows unchanged. Source likelihood positivity is not reset or conditioned on future completion. Arbitrary endpoint emissions, periodic/reducible updates, unreachable classes and countable accumulating rates remain in scope. Theorem 1.5 still requires real-risk/excess, its original constant suspended alpha transport, clipping/distortion and separator; this unit asserts no physical exact-real sampling or fixed COMPLETE-budget certificate.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowRisks.native_common_stationary_four_risks`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowRisks.native_complete_common_rows`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowRisks.native_orbit_original_risks`
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle](../../../Estimation/DataProcessing/MeasurableTotalVariationTriangle.md)
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits](NativePaidHistoryCommonRowLimits.md)
