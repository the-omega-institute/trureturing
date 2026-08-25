# Clock Time Versus Refinement Depth

## Abstract

Clock time alone does not determine predictive refinement depth.

**Theorem 1.1 (Clock duration and refinement depth separate).**

$$(\exists tauL: Unit \to Unit, qL: Unit \to Unit,\ (\forall n\in \mathbb{N}, \operatorname{iterate}\left(tauL, n, *\right) = *) \land \operatorname{completionDepth}\left(tauL, qL\right) = 0) \land 
(\exists tauD: DelayedState \to DelayedState, qD: DelayedState \to Bool,\ \operatorname{tauD}\left(zero\right) = one \land 2 \leq \operatorname{completionDepth}\left(tauD, qD\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/PredictionCertificates/ClockTimeVersusRefinementDepth.clock_time_does_not_determine_refinement_depth` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first witness is the one-state system. Its update and readout are both identities, so every finite number of clock updates returns the unique state while its predictive completion depth is zero.

The second witness is a four-state cycle whose readout is false at zero, one, and two, and true only at reveal. One update carries zero to one, but those two starting states cannot be distinguished at depth zero or one and are distinguished at depth two. Their least distinguishing time, and hence the system's completion depth, is therefore at least two.

Together the witnesses separate elapsed clock time from predictive refinement depth in these two concrete regimes. The result does not assert witnesses for every possible refinement depth.

## References

- Truth anchor: `D5/S3/ObserverMemory/PredictionCertificates/ClockTimeVersusRefinementDepth.clock_time_does_not_determine_refinement_depth`
- Dependency: [D5/S3/ObserverMemory/Prediction/ItineraryCompletion](../Prediction/ItineraryCompletion.md)
