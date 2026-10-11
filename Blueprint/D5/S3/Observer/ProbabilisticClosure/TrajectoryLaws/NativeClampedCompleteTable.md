# The original suspended-emission gap

## Abstract

NativeClampedCompleteTable

**Theorem 1.1 (An actual native regular comparison table).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall pi:PMFZ, (\forall tau:PMFZ, (\forall hB:ForwardStationarity, (\forall hA:BackwardStationarity, (\forall hX:PControlOnSupport, (\forall hY:BetaControlOnSupport, (\forall hcB:ForwardSupportClosure, (\forall hcA:BackwardSupportClosure, (\operatorname{NativeClampedCompleteDistortion}(Z, M, e, pi, tau, hB, hA, hX, hY, hcB, hcA))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeClampedCompleteTable.native_clamped_complete_distortion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Z is the original finite measurable COMPLETE configuration carrier. M is the original source-independent Observer and e is lawful. pi and tau are PMFs with pi.bind(update read1)=tau and tau.bind(update read0)=pi. Their positive supports project to active p and beta, and every acquired successor of either support lies in the other support, including successors whose original emission probability is zero. The table uses precisely these support types, PMF real weights and original update entries; no division or emission-weighted stationarity is used. Its u and v clamp the original read0 probabilities, and its Q and W are the actual rawTailLaw of clampedEmitter. Every generation, normalization and margin field is proved. The comparison has the same B,A,pi,tau and satisfies the two stationary weighted inequalities and the bounds (15du+10dv)/11 and (6du+15dv)/11. The comparison includes every complete RawTail event and the original law none mass.

**Theorem 1.2 (Strict gap for the unchanged original observer).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall mu:PMFPositiveDepth, (\forall ha:PositiveDepthOneMass, (\forall hb:PositiveDepthTwoMass, (\forall hc:OriginalReachableFibreSuspendedConstant, (\operatorname{OriginalConstantSuspensionGap}(Z, M, e, mu, ha, hb, hc))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeClampedCompleteTable.original_constant_suspension_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Z is any finite COMPLETE carrier with a measurable singleton structure. M has its original source-independent initialization and acquired kernels, e is any lawful InstalledEmitter M, and mu is any finite or countable PMF on positive Depth with nonzero mass at depthA=1 and depthB=2. SuspendedConstant means one s0 in [0,1] is the original read0 probability at every positive original configuration following every positive finite PhaseHistory beta whose current finite fields are the designated seed1 marker100 heldFields beta. All other held fibres and p configurations remain unrestricted. phaseExcess(s) is the real value of installedRisk(M,e,mu,s) minus rho(s), with rho(p)=1116529/22781250 and rho(beta)=239/6750. installedRisk is the supremum of original full configuration-before-TV loss over all original positive fourth-phase histories, including both seeds, rejection histories, partial parses, returns, records and pending matching Stop. The risk is uniformly at most one and finite; the subtraction here is real subtraction. Both excesses are nonnegative and their maximum is strictly greater than 1/195200. One native common pi,tau pair is acquired before all supported depths. Its original positive-history witnesses transport s0 to every positive beta support; clamping yields constant clamp(s0) without requiring global constancy. The two endpoint configuration risks give du<=2ep and dv<=2eb. Complete-law distortion gives DQ<=(30ep+20eb)/11 and DW<=(12ep+30eb)/11. The actual averaged configuration losses and these distortions imply full-event allowances hp=(41ep+20eb)/11 and hb=(12ep+41eb)/11. The constant_suspension_separator yields max(hp,hb)>1/35200; each allowance is at most (61/11)max(ep,eb), giving the strict bound. The full renderer correspondence uses each actual current held-record fibre through native_history_risk_transport. Comparison distortion averaged under pi,tau is not a worst-history risk bound for the modified emitter. The construction asserts neither an executable exact-real sampler nor fixed-resource preservation.

The consequences use the same original risks and reachable designated fibre. The maximum of the two real excesses in the constant-suspension class exceeds 1/195200, so the infimum over that entire class is at least 1/195200. The class is nonempty: the original finite control observer with a lawful deterministic read0 emitter and an endpoint-only prior is constant on that fibre. This infimum statement does not assert attainment. If both original configuration excesses equal zero, the observer cannot be constant. The designated fibre is nonempty by the common-row positive-history witness. If all its reachable read0 probabilities agreed with any one reachable value, that value lies in [0,1] and would supply SuspendedConstant. Thus failure of constancy provides two original positive histories and configurations on the fibre with distinct probabilities. For a sequence of arbitrary original observers, whose finite carriers and priors may vary, convergence of both configuration excesses to zero implies convergence of their maximum to zero. The maximum is eventually below 1/195200, so every sufficiently late observer has these two distinct reachable probabilities. No vanishing family, unrestricted optimum, unrestricted positive infimum or attainment is asserted.

The noncompletion boundary is a phase pair with one state per phase, acquired B=A=1, original u=0 and v=1, and both original raw laws delta_none. Both original all-event generation equations hold, yet original survival is one. Clamping gives uprime=1/3 and vprime=2/5. The comparison laws have zero none mass and their complete total variations from delta_none are one. Both weighted perturbation bounds are equalities: 1=1/3+(2/3)1 and 1=3/5+(2/5)1. The stationary-weighted proof therefore retains the original none atom and never assumes contraction of the original generator. Averaging two opposite deterministic laws can make their mean equal the source while retaining positive average configuration TV; the clipping argument uses configuration loss before TV. Acquired identity and periodic kernels preserve their stationary rows without mixing, whereas multiplying those rows by emission probabilities generally destroys acquired stationarity. Positive transient history weights need not remain positive in the stationary row; the native positive-history witness supplies the direction used by the theorem.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeClampedCompleteTable.native_clamped_complete_distortion`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeClampedCompleteTable.original_constant_suspension_gap`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/CompleteTailGeometricSurvival](CompleteTailGeometricSurvival.md)
