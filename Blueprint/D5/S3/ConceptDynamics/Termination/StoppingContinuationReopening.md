# Stopping, Continuation, and Reopening

## Abstract

Fixed stages can close while persistent parameter changes repeatedly create new defects.

**Theorem 1.1 (Stagewise completion coexists with infinite genuine reopening).**

$$\begin{aligned}(\operatorname{Closed}\left(q, T\right) \Leftrightarrow \operatorname{defectRelation}\left(q, T\right) = \emptyset) \land\\(\operatorname{ApproximatelyClosed}\left(q, T, \varepsilon\right) \Leftrightarrow \operatorname{worstFiberDefect}\left(q, T\right) \le \varepsilon) \land\\(\operatorname{BudgetStop}\left(c, Gain, L, \lambda\right) \Leftrightarrow \operatorname{sSup}\left(\{\frac{Gain\left(d\right)}{c\left(d\right)} \mid c\left(d\right) \le L\}\right) \le \lambda) \land\\(\operatorname{MethodStopped}\left(M, S, E, NoProposal\right) \Leftrightarrow M\left(S, E\right) = NoProposal) \land\\(\operatorname{LocallyComplete}\left(P, q\right) \Leftrightarrow \operatorname{ApproximatelyClosed}\left(\operatorname{restrict}\left(q, \operatorname{objectDomain}\left(P\right)\right), \operatorname{restrict}\left(\operatorname{target}\left(P\right), \operatorname{objectDomain}\left(P\right)\right), \operatorname{precision}\left(P\right)\right)) \land\\(\operatorname{OpenWorldSequence}\left(P\right) \Leftrightarrow \left(\left(\forall n \in Nat,\; \operatorname{objectDomain}\left(P\left(n\right)\right) \ne \operatorname{objectDomain}\left(P\left(n + 1\right)\right)\right) \lor \left(\left(\forall n \in Nat,\; \operatorname{target}\left(P\left(n\right)\right) \ne \operatorname{target}\left(P\left(n + 1\right)\right)\right) \lor \left(\left(\forall n \in Nat,\; \operatorname{precision}\left(P\left(n\right)\right) \ne \operatorname{precision}\left(P\left(n + 1\right)\right)\right) \lor \left(\forall n \in Nat,\; \operatorname{operationFamily}\left(P\left(n\right)\right) \ne \operatorname{operationFamily}\left(P\left(n + 1\right)\right)\right)\right)\right)\right)) \land\\(\operatorname{Reopens}\left(P0, P1, D0, D1, q\right) \Leftrightarrow \left(\left(\operatorname{objectDomain}\left(P0\right) \ne \operatorname{objectDomain}\left(P1\right) \lor \left(\operatorname{target}\left(P0\right) \ne \operatorname{target}\left(P1\right) \lor \left(\operatorname{precision}\left(P0\right) \ne \operatorname{precision}\left(P1\right) \lor \left(\operatorname{operationFamily}\left(P0\right) \ne \operatorname{operationFamily}\left(P1\right) \lor D0 \ne D1\right)\right)\right)\right) \land \operatorname{Nonempty}\left((\operatorname{inter}\left(\operatorname{defectRelation}\left(q, \operatorname{target}\left(P1\right)\right), \operatorname{square}\left(\operatorname{objectDomain}\left(P1\right)\right)\right)) \setminus (\operatorname{inter}\left(\operatorname{defectRelation}\left(q, \operatorname{target}\left(P0\right)\right), \operatorname{square}\left(\operatorname{objectDomain}\left(P0\right)\right)\right))\right)\right)) \land\\\exists P \in Nat \to \operatorname{LocalParameters}\left(Nat, Real, Unit\right), D \in Nat \to \operatorname{Set}\left(Unit\right), Q \in Nat \to \operatorname{Concept}\left(Nat, Real\right),\; \left(\forall n \in Nat,\; \operatorname{Nonempty}\left(\operatorname{objectDomain}\left(P\left(n\right)\right)\right)\right) \land \left(\operatorname{OpenWorldSequence}\left(P\right) \land \left(\left(\forall n \in Nat,\; \operatorname{LocallyComplete}\left(P\left(n\right), Q\left(n\right)\right)\right) \land \operatorname{FrequentlyAtTop}\left(\{n \mid \operatorname{Reopens}\left(P\left(n\right), P\left(n + 1\right), D\left(n\right), D\left(n + 1\right), Q\left(n\right)\right)\}\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Termination/StoppingContinuationReopening.stopping_continuation_reopening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The stopping conjuncts give exact source definitions. Target closure uses the canonical `defectRelation`; approximate closure uses the supremum of metric target diameters over readout fibers. Empty fibers contribute zero and unbounded diameters contribute top. Budget stopping is the displayed real `sSup` formula itself; only its useful pointwise characterization assumes a nonempty feasible set and a bounded-above ratio set. Method stopping is the literal value equation.

Local completion checks the supplied domain, target, and precision; the source gives no operation-family action on that closure predicate. An open-world sequence has one fixed field that changes at every adjacent stage. A reopening requires one of the five allowed changes and a canonical defect pair present after the change but absent before.

The final conjunct exhibits natural-number stages with nonempty object domains and real-valued targets. Each fixed stage is closed, while every transition changes the target and creates a nonempty defect. Hence reopening occurs frequently at `atTop`.

No finiteness, decidable equality, measurability, nonempty-domain premise, monotonicity, or extra order law is added. The target metric is exactly the structure requested by approximate closure.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Termination/StoppingContinuationReopening.stopping_continuation_reopening`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
