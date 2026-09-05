# Golden Shadow Operator

## Abstract

A positive operator satisfying the golden shadow identity is the inverse-golden scalar on every nonzero active Hilbert space.

**Theorem 1.1 (The golden identity collapses the active operator spectrum).**

$$\begin{gathered}\forall E: \operatorname{Type}(),\\{}[\operatorname{NormedAddCommGroup}(E)] \land [\operatorname{InnerProductSpace}(\mathbb{C}, E)] \land [\operatorname{CompleteSpace}(E)] \land [\operatorname{Nontrivial}(E)],\\{}\forall D: \operatorname{ContinuousLinearMap}(\mathbb{C}, E, E), (0 \leq D \land I = D + D^{2}) \Rightarrow\\{}(D = \operatorname{algebraMap}(\mathbb{R}, \operatorname{ContinuousLinearMap}(\mathbb{C}, E, E), \phi^{-1}) \land\\{}I - D = \operatorname{algebraMap}(\mathbb{R}, \operatorname{ContinuousLinearMap}(\mathbb{C}, E, E), {\phi^{-1}}^{2}) \land\\{}D^{2} = \operatorname{algebraMap}(\mathbb{R}, \operatorname{ContinuousLinearMap}(\mathbb{C}, E, E), {\phi^{-1}}^{2}) \land\\{}\operatorname{spectrum}(\mathbb{R}, D) = \{\phi^{-1}\} \land\\{}\left\lVert D \right\rVert = \phi^{-1}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenShadowOperator.golden_shadow_operator_theorem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let D be a positive continuous endomorphism of a nontrivial complex Hilbert space. If I equals D plus D squared, continuous functional calculus makes every real spectral value satisfy the same quadratic.

Positivity excludes the negative root. Thus D is the inverse-golden scalar operator; its complement and square are both the inverse-golden-square scalar operator, and its spectrum and norm have the displayed exact values.

The source's contraction hypothesis is omitted because the exact norm conclusion already implies it. Nontriviality of the active space is stated explicitly: on the zero space the operator identity still holds, but the spectrum is empty and the norm is zero.

Repository, receipt, digest, generalized-result, and in-flight branch searches found no equivalent theorem. GoldenTwoShadowBound gives the neighboring sharp inequalities, not this equality-case collapse.

## References

- Truth anchor: `D5/S3/Observer/GoldenShadowOperator.golden_shadow_operator_theorem`
