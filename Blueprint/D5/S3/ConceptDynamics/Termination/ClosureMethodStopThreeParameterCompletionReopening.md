# Closure, Method Stop, and Three-Parameter Completion/Reopening

## Abstract

Exact and approximate closure support method stopping and three-parameter completion/reopening.

**Theorem 1.1 (Closure, method stop, and three-parameter completion/reopening).**

$$\left(\operatorname{Closed}\left(q, T\right) \Leftrightarrow \operatorname{defectRelation}\left(q, T\right) = \emptyset\right) \land \left(\left([\operatorname{MetricSpace}(T)] \Rightarrow \left(\operatorname{ApproximatelyClosed}\left(q, T, (\varepsilon: \operatorname{NNReal})\right) \Leftrightarrow \operatorname{worstFiberDefect}\left(q, T\right) \le \operatorname{coeENNReal}\left((\varepsilon: \operatorname{NNReal})\right)\right)\right) \land \left(\left(\operatorname{MethodStopped}\left(M, S, E, NoProposal\right) \Leftrightarrow M\left(S, E\right) = NoProposal\right) \land \left(\left([\operatorname{MetricSpace}(T)] \Rightarrow \left(\operatorname{ThreeParameterLocallyComplete}\left(P, q\right) \Leftrightarrow \operatorname{ApproximatelyClosed}\left(\operatorname{restrict}\left(q, \operatorname{objectDomain}\left(P\right)\right), \operatorname{restrict}\left(\operatorname{target}\left(P\right), \operatorname{objectDomain}\left(P\right)\right), \operatorname{precision}\left(P\right)\right)\right)\right) \land \left([\operatorname{MetricSpace}(T)] \Rightarrow \left(\operatorname{ThreeParameterReopens}\left(P0, P1, q\right) \Leftrightarrow \left(\left(\operatorname{objectDomain}\left(P0\right) \ne \operatorname{objectDomain}\left(P1\right) \lor \left(\operatorname{target}\left(P0\right) \ne \operatorname{target}\left(P1\right) \lor \operatorname{precision}\left(P0\right) \ne \operatorname{precision}\left(P1\right)\right)\right) \land \operatorname{Nonempty}\left((\operatorname{inter}\left(\operatorname{inter}\left(\operatorname{defectRelation}\left(q, \operatorname{target}\left(P1\right)\right), \operatorname{distanceAbove}\left(\operatorname{target}\left(P1\right), \operatorname{precision}\left(P1\right)\right)\right), \operatorname{square}\left(\operatorname{objectDomain}\left(P1\right)\right)\right)) \setminus (\operatorname{inter}\left(\operatorname{inter}\left(\operatorname{defectRelation}\left(q, \operatorname{target}\left(P0\right)\right), \operatorname{distanceAbove}\left(\operatorname{target}\left(P0\right), \operatorname{precision}\left(P0\right)\right)\right), \operatorname{square}\left(\operatorname{objectDomain}\left(P0\right)\right)\right))\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Termination/ClosureMethodStopThreeParameterCompletionReopening.closure_method_stop_three_parameter_completion_reopening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The package records five formalized assertions. Target closure uses the canonical `defectRelation`; approximate closure uses the supremum of metric target diameters over readout fibers against a finite nonnegative tolerance chosen by this formalization. Empty fibers contribute zero and unbounded diameters contribute top. Method stopping is the literal distinguished-value equation.

Three-parameter local completion checks the supplied domain, target, and finite precision. A three-parameter reopening requires one of those parameters to change and a canonical defect pair above the next precision that was absent above the current precision.

Unresolved source gaps: section 5 defines a language-blind residual and section 44 defines operation-induced observational equivalence, but section 43 does not identify either construction with its stage readout or residual, nor give a transition map to a new stage residual. This formalization covers only the object-domain, target, and precision triggers.

Section 9.1 assumes a metric and explicitly uses tolerance zero, but it does not type the tolerance or decide whether negative tolerances are allowed. Lean conventionally uses `NNReal`; this is not presented as an exact source-domain match and must be reopened if the source later admits negative tolerance.

No finiteness, decidable equality, measurability, nonempty-domain premise, monotonicity, or extra order law is added. The target metric is exactly the structure requested by approximate closure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Termination/ClosureMethodStopThreeParameterCompletionReopening.closure_method_stop_three_parameter_completion_reopening`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
