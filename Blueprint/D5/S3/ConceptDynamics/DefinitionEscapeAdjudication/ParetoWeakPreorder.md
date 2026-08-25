# Pareto Weak Dominance Preorder

## Abstract

Five independently preordered gain coordinates induce a preorder of actions.

**Theorem 1.1 (Weak Pareto dominance is reflexive and transitive).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}\operatorname{Preorder}\left(Information\right), \operatorname{Preorder}\left(Residual\right), \operatorname{Preorder}\left(Transfer\right), \operatorname{Preorder}\left(Cost\right), \operatorname{Preorder}\left(Risk\right),\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right),\\{}(\forall a: Action, \operatorname{ParetoWeak}\left(value, a, a\right)) \land\\{}(\forall a, b, c: Action, \operatorname{ParetoWeak}\left(value, a, b\right) \Rightarrow \operatorname{ParetoWeak}\left(value, b, c\right) \Rightarrow \operatorname{ParetoWeak}\left(value, a, c\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoWeakPreorder.pareto_weak_reflexive_transitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Information, residual capture, and transfer are benefit coordinates; lifecycle cost and risk are burden coordinates. Weak dominance therefore reverses the comparison direction on the final two coordinates.

Coordinate reflexivity proves self-dominance. Coordinate transitivity composes two dominance comparisons, independently in all five heterogeneous preorder types.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoWeakPreorder.pareto_weak_reflexive_transitive`
