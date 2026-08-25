# Stopping, Continuation, and Reopening

## Abstract

Stopping and continuation expose when parameter changes create new defects.

**Theorem 1.1 (Stopping, continuation, and reopening).**

$$\left(\operatorname{Closed}\left(q, T\right) \Leftrightarrow \operatorname{defectRelation}\left(q, T\right) = \emptyset\right) \land \left(\left(\operatorname{ApproximatelyClosed}\left(q, T, \varepsilon\right) \Leftrightarrow \operatorname{worstFiberDefect}\left(q, T\right) \le \varepsilon\right) \land \left(\left(\operatorname{MethodStopped}\left(M, S, E, NoProposal\right) \Leftrightarrow M\left(S, E\right) = NoProposal\right) \land \left(\left(\operatorname{LocallyComplete}\left(P, q\right) \Leftrightarrow \operatorname{ApproximatelyClosed}\left(\operatorname{restrict}\left(q, \operatorname{objectDomain}\left(P\right)\right), \operatorname{restrict}\left(\operatorname{target}\left(P\right), \operatorname{objectDomain}\left(P\right)\right), \operatorname{precision}\left(P\right)\right)\right) \land \left(\operatorname{Reopens}\left(P0, P1, D0, D1, q\right) \Leftrightarrow \left(\left(\operatorname{objectDomain}\left(P0\right) \ne \operatorname{objectDomain}\left(P1\right) \lor \left(\operatorname{target}\left(P0\right) \ne \operatorname{target}\left(P1\right) \lor \left(\operatorname{precision}\left(P0\right) \ne \operatorname{precision}\left(P1\right) \lor \left(\operatorname{operationFamily}\left(P0\right) \ne \operatorname{operationFamily}\left(P1\right) \lor D0 \ne D1\right)\right)\right)\right) \land \operatorname{Nonempty}\left((\operatorname{inter}\left(\operatorname{inter}\left(\operatorname{defectRelation}\left(q, \operatorname{target}\left(P1\right)\right), \operatorname{distanceAbove}\left(\operatorname{target}\left(P1\right), \operatorname{precision}\left(P1\right)\right)\right), \operatorname{square}\left(\operatorname{objectDomain}\left(P1\right)\right)\right)) \setminus (\operatorname{inter}\left(\operatorname{inter}\left(\operatorname{defectRelation}\left(q, \operatorname{target}\left(P0\right)\right), \operatorname{distanceAbove}\left(\operatorname{target}\left(P0\right), \operatorname{precision}\left(P0\right)\right)\right), \operatorname{square}\left(\operatorname{objectDomain}\left(P0\right)\right)\right))\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Termination/StoppingContinuationReopening.stopping_continuation_reopening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The package records five retained source assertions. Target closure uses the canonical `defectRelation`; approximate closure uses the supremum of metric target diameters over readout fibers. Empty fibers contribute zero and unbounded diameters contribute top. Method stopping is the literal distinguished-value equation.

Local completion checks the supplied domain, target, and precision; the source gives no operation-family action on that closure predicate. A reopening requires one of the allowed parameter or language changes and a canonical defect pair above the next precision that was absent above the current precision.

The source supplies no mechanism by which a definition-language change alters the readout or residual family. The change remains an allowed trigger, but this document does not invent a language action.

No finiteness, decidable equality, measurability, nonempty-domain premise, monotonicity, or extra order law is added. The target metric is exactly the structure requested by approximate closure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Termination/StoppingContinuationReopening.stopping_continuation_reopening`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
