# Symmetric Pareto Kernel and Vector Equality

## Abstract

Under coordinate partial orders, the symmetric Pareto kernel is equality of gain vectors.

**Theorem 1.1 (The symmetric kernel is exactly gain-vector equality).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{DecidableEq}\left(Action\right)], \operatorname{PartialOrder}\left(Information\right), \operatorname{PartialOrder}\left(Residual\right), \operatorname{PartialOrder}\left(Transfer\right),\\{}\operatorname{PartialOrder}\left(Cost\right), \operatorname{PartialOrder}\left(Risk\right),\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right), F: \operatorname{Finset}\left(Action\right),\\{}x, y: \operatorname{ParetoCarrier}\left(F\right),\\{}\operatorname{ParetoEqOn}\left(value, F, x, y\right) \iff value(x.1) = value(y.1).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnVectorEquality.pareto_eq_on_iff_vector_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each benefit coordinate is compared in its given direction, while lifecycle cost and risk use the reversed burden direction inherited from weak Pareto dominance.

Antisymmetry in all five partial orders turns the two independent dominance directions into equality of every coordinate; the converse is coordinate reflexivity.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnVectorEquality.pareto_eq_on_iff_vector_eq`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoEqOnDecidableEquivalence](ParetoEqOnDecidableEquivalence.md)
