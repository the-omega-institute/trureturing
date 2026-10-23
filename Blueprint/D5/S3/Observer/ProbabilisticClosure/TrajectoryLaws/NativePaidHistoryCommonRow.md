# Native paid-history law control

## Abstract

Native paid-history law control

The original finite COMPLETE carrier, source-independent M.init and ordered acquired M.update are retained. Alpha is read 0 and beta is read 1. The literal suffix S=reads[1,0,1,1,0,0] accepts seed 1 and writes marker 100 before the held fourth latch. Every window and every appended return is an actual finite paid history; the average of their rows is never asserted to be a posterior row of one history.

**Theorem 1.1 (Literal native paid-window control).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall e:InstalledEmitterM, (\forall mu:PMFDepth, (\forall m:Natural, (\forall t:Natural, (\forall j:Natural, (\forall s:ActivePhase, (\operatorname{NativeWindowFacts}(Z, M, e, mu, m, t, j, s)))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.native_paid_window_control` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

NativeWindowFacts denotes the full conjunction in the Lean telescope: render and reconstruct the actual operation list, exact alpha/beta counts, positive depth likelihoods and positive original normalizer, actual row support on the held active fibre, the copied original fullLaw identity through fullRenderer, configuration and law bounds with their distinct original phase suprema, equality of raw and installed law risk, the quadratic log-ratio envelope and strict native competing-depth entropy. The original all-PhaseHistory suprema include every rejection and return.

**Theorem 1.2 (Quadratic control on growing windows).**

$$\forall k:Depth, (\forall i:Depth, (\forall w:Natural, (\forall u:Natural, (\forall v:Natural, (\forall j:Natural, (\forall s:ActivePhase, (\operatorname{GrowingWindowLikelihood}(k, i, w, u, v, j, s))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.native_growing_window_likelihood` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For w>=2 and u,v<w, set N=w^3, m=floor(N*r_k)+u and t=floor(N*(1-r_k))+v. GrowingWindowLikelihood is log(L_i/L_k)<=18/w+suffixLogRatio(j,s,k,i). The proof uses r_k(1-r_k)>=2/9 and the quadratic empirical Bernoulli log inequality. The fixed latch and return likelihood factors are retained. This is a uniform upper envelope, not a uniform positive depth gap.

**Theorem 1.3 (Uniform posterior collapse for each supported depth).**

$$\forall mu:PMFDepth, (\forall k:SupportedDepthMu, (\forall j:Natural, (\forall s:ActivePhase, (\operatorname{UniformPosteriorCollapse}(mu, k, j, s)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.native_countable_posterior_concentration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

UniformPosteriorCollapse means: for each epsilon>0, eventually w>=2 and for every u,v<w the original posterior of the actual window at k has 1-posterior(k).toReal<epsilon. The prior is one arbitrary PMF on positive integers, including countable accumulating native rates. Strict native KL gives each fixed competitor cubic decay; the min of that decay and exp(16+2*j) dominates every finite-window competitor. Original prior weights supply a summable envelope, and pinned Tannery dominated convergence closes the countable sum. Fixed return words do not change the prior or conditioning.

**Theorem 1.4 (Complete countable target convergence in total variation).**

$$\forall mu:PMFDepth, (\forall k:SupportedDepthMu, (\forall j:Natural, (\forall s:ActivePhase, (\operatorname{UniformCompleteTargetTV}(mu, k, j, s)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.native_countable_target_concentration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

UniformCompleteTargetTV has the same epsilon, eventual-window and all-offset quantifiers as posterior collapse. Its error is measurableTotalVariation(rawTarget(mu,H),pureTail(k,s)).toReal. pureTail is the original rawReadLaw(r_k) mapped by validStopped, including the noncompletion outcome. The original conditional target is the countable posterior mixture of these complete laws; its total variation from the supported atom law is at most 1-posterior(k). No finite TV vector substitutes for this countable law.

**Theorem 1.5 (Invariant generator agreement preserves the entire infinite law).**

$$\forall Z:FiniteMeasurableSingletonType, (\forall M:ObserverZ, (\forall N:ObserverZ, (\forall e:InstalledEmitterM, (\forall f:InstalledEmitterN, (\forall G:InvariantConfigurations, (\forall z:ConfigurationInG, (\operatorname{InstalledLawInvariant}(Z, M, N, e, f, G, z))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.installed_law_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

InstalledLawInvariant assumes the same projected native fields, equality of the marked acquired generators on G and closure of their original positive supports. It proves equality of markedLaw on the entire infinite path space, then of fullLaw and every tailLaw. Prefix coupling gives equality and support propagation at each finite cut. The original path_ext supplier applies projective uniqueness to extend those equalities to all measurable infinite events. This preserves noncompletion, rather than inferring almost-sure completion from finite-word recursion.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.installed_law_invariant`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.native_countable_posterior_concentration`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.native_countable_target_concentration`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.native_growing_window_likelihood`
- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRow.native_paid_window_control`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeInstalledFullLaw](NativeInstalledFullLaw.md)
