# Stopping, Continuation, and Reopening

## Abstract

Fixed stages can close while persistent parameter changes repeatedly create new defects.

**Theorem 1.1 (Stagewise completion coexists with infinite genuine reopening).**

$$\begin{aligned}(\operatorname{Closed}\left(q, T\right) \Leftrightarrow \operatorname{defectRelation}\left(q, T\right) = \emptyset) \land\\(\operatorname{ApproximatelyClosed}\left(\Delta, q, T, \varepsilon\right) \Leftrightarrow \Delta\left(q, T\right) \le \varepsilon) \land\\(\operatorname{BudgetStop}\left(c, Gain, L, \lambda\right) \Leftrightarrow \left(\forall d \in Decision,\; c\left(d\right) \le L \Rightarrow \frac{Gain\left(d\right)}{c\left(d\right)} \le \lambda\right)) \land\\(\left(\operatorname{Nonempty}\left(\{d \mid c\left(d\right) \le L\}\right) \land \operatorname{BddAbove}\left(\{\frac{Gain\left(d\right)}{c\left(d\right)} \mid c\left(d\right) \le L\}\right)\right) \Rightarrow \left(\operatorname{BudgetStop}\left(c, Gain, L, \lambda\right) \Leftrightarrow \operatorname{sSup}\left(\{\frac{Gain\left(d\right)}{c\left(d\right)} \mid c\left(d\right) \le L\}\right) \le \lambda\right)) \land\\(\operatorname{MethodStopped}\left(M, S, E, NoProposal\right) \Leftrightarrow M\left(S, E\right) = NoProposal) \land\\(\operatorname{LocallyComplete}\left(\operatorname{LocalParameters}\left(X, T, I, \varepsilon\right), q\right) \Leftrightarrow \operatorname{Closed}\left(\operatorname{restrict}\left(q, X\right), \operatorname{restrict}\left(T, X\right)\right)) \land\\(\operatorname{OpenWorldSequence}\left(P\right) \Leftrightarrow \left(\forall n \in Nat,\; \operatorname{objectDomain}\left(P\left(n\right)\right) \ne \operatorname{objectDomain}\left(P\left(n + 1\right)\right) \lor \left(\operatorname{target}\left(P\left(n\right)\right) \ne \operatorname{target}\left(P\left(n + 1\right)\right) \lor \left(\operatorname{operationFamily}\left(P\left(n\right)\right) \ne \operatorname{operationFamily}\left(P\left(n + 1\right)\right) \lor \operatorname{precision}\left(P\left(n\right)\right) \ne \operatorname{precision}\left(P\left(n + 1\right)\right)\right)\right)\right)) \land\\(\operatorname{Reopens}\left(P0, P1, D0, D1, q\right) \Leftrightarrow \left(\left(\operatorname{objectDomain}\left(P0\right) \ne \operatorname{objectDomain}\left(P1\right) \lor \left(\operatorname{target}\left(P0\right) \ne \operatorname{target}\left(P1\right) \lor \left(\operatorname{precision}\left(P0\right) \ne \operatorname{precision}\left(P1\right) \lor \left(\operatorname{operationFamily}\left(P0\right) \ne \operatorname{operationFamily}\left(P1\right) \lor D0 \ne D1\right)\right)\right)\right) \land \operatorname{Nonempty}\left(\operatorname{defectRelation}\left(\operatorname{restrict}\left(q, \operatorname{objectDomain}\left(P1\right)\right), \operatorname{restrict}\left(\operatorname{target}\left(P1\right), \operatorname{objectDomain}\left(P1\right)\right)\right)\right)\right)) \land\\\exists P \in Nat \to \operatorname{LocalParameters}\left(Nat, Bool, Unit, Nat\right), D \in Nat \to \operatorname{Set}\left(Unit\right), Q \in Nat \to \operatorname{Concept}\left(Nat, Bool\right),\; \operatorname{Nonempty}\left(Bool\right) \land \left(\left(\forall n \in Nat,\; \operatorname{Nonempty}\left(\operatorname{objectDomain}\left(P\left(n\right)\right)\right)\right) \land \left(\operatorname{OpenWorldSequence}\left(P\right) \land \left(\left(\forall n \in Nat,\; \operatorname{LocallyComplete}\left(P\left(n\right), Q\left(n\right)\right)\right) \land \operatorname{FrequentlyAtTop}\left(\{n \mid \operatorname{Reopens}\left(P\left(n\right), P\left(n + 1\right), D\left(n\right), D\left(n + 1\right), Q\left(n\right)\right)\}\right)\right)\right)\right)\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Termination/StoppingContinuationReopening.stopping_continuation_reopening` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first five conjuncts give exact stopping definitions. Target closure uses the canonical `defectRelation`; approximate closure uses the supplied comparison; and budget stopping uses a total pointwise condition. For real ratios it agrees with the displayed `sSup` formula when the feasible set is nonempty and the ratio set is bounded above. Method stopping is the literal method value equation.

Local completion fixes all four parameters `(X,T,I,epsilon)`. An open-world sequence changes at least one of them at every adjacent stage. A reopening requires both one of the five allowed changes, including definition language, and a nonempty canonical defect on the next object domain.

The final conjunct exhibits natural-number stages with nonempty object domains and a nonempty Boolean target type. Each fixed stage is closed, while every transition changes the target and creates a nonempty defect. Hence reopening occurs frequently at `atTop`.

The comparison and division symbols denote only the supplied generic operations. No finiteness, decidable equality, measurability, nonempty-domain premise, monotonicity, or order laws are added to the generic stopping definitions.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Termination/StoppingContinuationReopening.stopping_continuation_reopening`
- Dependency: [D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff](../TargetRisk/RefinementRiskCostTradeoff.md)
