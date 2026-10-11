# Stationary weighted complete-law distortion

## Abstract

CompleteTailWeightedDistortion

**Theorem 1.1 (Distortion with primed continuation coefficients).**

$$\forall X:FiniteType, (\forall Y:FiniteType, (\forall R:RegularTableXY, (\forall u:XToReal, (\forall v:YToReal, (\forall Q:XToProbabilityRawLaw, (\forall W:YToProbabilityRawLaw, (\forall hq:OriginalPGeneration, (\forall hw:OriginalBetaGeneration, (\operatorname{StationaryWeightedCompleteDistortion}(X, Y, R, u, v, Q, W, hq, hw))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailWeightedDistortion.stationary_weighted_complete_distortion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

X and Y are arbitrary finite types. R is a RegularTable on X and Y, with normalized nonnegative rows, common stationarity, clamped u and v in [1/3,2/5], probability complete laws Qprime and Wprime, and their all-event generation equations. u and v are arbitrary real functions. Q and W are probability laws and satisfy the stated original all-event generation equations with the same B and A. For du=sum pi abs(u-uprime), dv=sum tau abs(v-vprime), DQ=sum pi TV(Q,Qprime).toReal and DW=sum tau TV(W,Wprime).toReal, DQ is at most du+(2/3)DW and DW is at most dv+(2/5)DQ. Thus DQ is at most (15du+10dv)/11 and DW is at most (6du+15dv)/11. The event supremum is taken at each configuration before the stationary average. The identity (u-uprime)(indicator-originalContinuation)+(1-uprime)(originalContinuation-primedContinuation) uses the primed continuation coefficient. The complete event domain includes the noncompletion atom. The original generator needs no contraction, properness or absolute continuity.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailWeightedDistortion.stationary_weighted_complete_distortion`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeEmissionClipping](NativeEmissionClipping.md)
