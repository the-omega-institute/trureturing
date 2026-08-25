# Gain Difference Cocycle

## Abstract

Five heterogeneous additive gain coordinates telescope exactly.

**Theorem 1.1 (Gain differences have zero self-value and a three-point cocycle).**

$$\begin{gathered}\forall Action, Information, Residual, Transfer, Cost, Risk: \operatorname{Type},\\{}[\operatorname{AddGroup}\left(Information\right)], [\operatorname{AddGroup}\left(Residual\right)], [\operatorname{AddGroup}\left(Transfer\right)], [\operatorname{AddGroup}\left(Cost\right)], [\operatorname{AddGroup}\left(Risk\right)],\\{}value: Action \to \operatorname{GainVector}\left(Information, Residual, Transfer, Cost, Risk\right),\\{}(\forall a: Action, \operatorname{gainDifference}\left(value, a, a\right) = 0) \land\\{}(\forall a, b, c: Action, \operatorname{gainDifference}\left(value, a, c\right) = \operatorname{gainDifference}\left(value, a, b\right) + \operatorname{gainDifference}\left(value, b, c\right)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/GainDifferenceCocycle.gain_difference_self_zero_and_cocycle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary action type, each action receives one vector with independently typed information, residual-capture, transfer, lifecycle-cost, and risk coordinates. Each coordinate is an additive group, and gainDifference subtracts absolute values coordinate by coordinate.

Scalar self-subtraction proves the first clause. In the second clause, the intermediate absolute value cancels independently in all five coordinates by sub_add_sub_cancel, yielding the direct difference.

This closes the first half of proof obligation 10 in definition-escape-completion-theory atom generic-residual-8f550f340a56075d2e0b7a070a3f78814a780adf06d7f6677736a277f7a39cb3. The separate no-source-weight implication is not asserted here.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/GainDifferenceCocycle.gain_difference_self_zero_and_cocycle`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscapeAdjudication/ParetoWeakPreorder](ParetoWeakPreorder.md)
