# Zero gain on the original margin

## Abstract

Stationary completion localization

F is an arbitrary original boxed Borel CommonFlow. CRow(F,Q) is its actual unweighted acquired return row. q is the decreasing harmonic limit of T to the power n applied to the positive three-step completion average, with T=L/(6/25). excess(Q)=g(Q).toReal-9/25 and sixthFunctional=q to the sixth power divided by threeStepAverage to the fifth power. AE(mu,Q,P) means P holds for mu-almost every Q.

**Theorem 1.1 (Stationarity earns zero excess on surviving mass).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, (\operatorname{lintegral}\left(\operatorname{CRow}\left(F, Q\right), R, \operatorname{sixthFunctional}\left(F, R\right)\right)=\operatorname{sixthFunctional}\left(F, Q\right)\land \operatorname{ofReal}\left(\operatorname{excess}\left(Q\right)\right) \cdot \operatorname{sixthFunctional}\left(F, Q\right)=0\land (\operatorname{q}\left(F, Q\right)\neq 0\Rightarrow\operatorname{excess}\left(Q\right)=0))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStationaryLocalization.common_flow_stationary_localization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original unweighted stationarity identity makes the integral of CF equal the integral of F. The earned bound CF >= F+(9/20)*excess*F and finiteness therefore give CF=F almost everywhere. Additive cancellation gives excess*F=0. When q is nonzero, positive finite h makes F nonzero; excess is nonnegative and hence equals zero. No harmonicity, zero-excess, stationarity-conditioned event, or path localization conclusion is added as a premise.

**Theorem 1.2 (The acquired edges preserve the stationary functional).**

$$\forall F: CommonFlow, \operatorname{AE}\left(\operatorname{nuP}\left(F\right), Q, \operatorname{AE}\left(\operatorname{CRow}\left(F, Q\right), R, \operatorname{sixthFunctional}\left(F, R\right)=\operatorname{sixthFunctional}\left(F, Q\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStationaryLocalization.common_flow_stationary_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Cauchy-Schwarz on each actual probability row gives (CF) squared <= C(F squared). The earned fixed point CF=F and original stationarity make the two second moments have the same integral, so equality holds almost everywhere. The real conditional variance is therefore zero. The bounded second moment and the pinned zero-variance theorem force F at the successor to equal F at the input on almost every acquired edge. No reversibility, deterministic successor or mixing condition is used.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStationaryLocalization.common_flow_stationary_edges`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelStationaryLocalization.common_flow_stationary_localization`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeBorelSuperharmonic](NativeBorelSuperharmonic.md)
