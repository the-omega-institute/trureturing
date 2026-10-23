# Relative-prior stability of complete native conditional tails

## Abstract

Relative-prior stability of complete native conditional tails.

PMFDepth is a probability mass function on the original positive integer Depth carrier, with arbitrary finite or countable support. ListOperation means the original List Operation. at(mu,k)=mu(k), ofReal is the canonical map into ENNReal, and TV is the event-supremum measurableTotalVariation. Both priors use the same rate(k), original source history cylinder and unread stopped-tail map. No bounded support, finite-depth cutoff or lower bound on individual positive prior masses is required.

The relative comparison includes common zero masses. For every finite legal h with run(h)=some(c), the native history normalizer is positive under each PMF. The complete rawTarget is the original jointLaw conditioned on nativeEvent(h,c), mapped by validStopped(s,rawTail(omega,length(readLetters(h)))). It retains every finite lawful completion and the unique infinite noncompletion coordinate. Neither an auxiliary posterior model nor a clipped law replaces that target.

**Theorem 1.1 (All finite legal histories and both active phases).**

$$\forall mu: PMFDepth, (\forall nu: PMFDepth, (\forall zeta: Real, (\forall h: ListOperation, (\forall c: AcquiredNativeState, (\forall s: ActivePhase, (((0\leq zeta)\land((zeta< 1)\land((\forall k: Depth, ((\operatorname{ofReal}(1-zeta) \cdot \operatorname{at}(mu,k)\leq \operatorname{at}(nu,k))\land(\operatorname{at}(nu,k)\leq \operatorname{ofReal}(1+zeta) \cdot \operatorname{at}(mu,k))))\land(\operatorname{run}(h)=\operatorname{some}(c)))))\Rightarrow(\operatorname{measurableTotalVariation}(\operatorname{rawTarget}(mu,h,c,s),\operatorname{rawTarget}(nu,h,c,s))\leq \operatorname{ofReal}(\frac{zeta}{1-zeta}))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeRelativePriorStability.native_relative_prior_tail` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original countable depth mixture inherits both event-wise prior bounds. Conditioning on the same positive history event gives the two normalized inequalities (1-zeta)P(E)<=(1+zeta)Q(E) and (1-zeta)Q(E)<=(1+zeta)P(E). Apply them to E and its complement; probability normalization bounds both directed differences by zeta. Taking the measurable-event supremum and mapping through the original validStopped map gives TV<=ofReal(zeta), which implies the displayed source bound zeta/(1-zeta). This estimate is uniform in history mass and length, including rare histories.

This is the complete raw stopped-configuration law subclause of Theorem 7.2 in RECURSIVE_RELATIONAL_OBSERVATION_ENDPOINT_FLOOR_HISTORY_LOCALIZATION. Rendering to full transcripts, observer row comparisons, both law-error orders, capped and uncapped risks and Phi, witness transfer and acquisition-cap certificates remain separate obligations. No assertion about a runtime prior oracle, effective computation, sharp optimal constant or research originality is made. The source-independent private-row and full-transcript transport suppliers are NativeObserverJointLaw.native_history_risk_transport and NativeFullResidual.full_renderer_tv.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeRelativePriorStability.native_relative_prior_tail`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw](NativeObserverJointLaw.md)
