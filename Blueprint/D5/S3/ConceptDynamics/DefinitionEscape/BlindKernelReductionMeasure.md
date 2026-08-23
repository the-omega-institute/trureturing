# Blind Kernel Reduction Measure

## Abstract

Positive weight detects blind residual pairs separated by a new definition.

**Theorem 1.1 (Positive reduction weight detects a separated blind pair).**

$$(\forall S,\ 0 \leq \nu(S)) \land (\forall S,\ 0 < \nu(S) \iff \operatorname{Nonempty}\left(S\right)) \Rightarrow\\{}(\operatorname{blindKernelReductionMeasure}\left(\nu, \Gamma, q, T, d\right) = \nu(\operatorname{intersection}\left(\operatorname{blindResidual}\left(\Gamma, q, T\right), \operatorname{complement}\left(\operatorname{ker}\left(d\right)\right)\right))) \land (0 \leq \operatorname{blindKernelReductionMeasure}\left(\nu, \Gamma, q, T, d\right)) \land\\{}(0 < \operatorname{blindKernelReductionMeasure}\left(\nu, \Gamma, q, T, d\right) \iff \exists p, p \in \operatorname{blindResidual}\left(\Gamma, q, T\right) \land d(p_{1}) \neq d(p_{2})).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelReductionMeasure.blind_kernel_reduction_measure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The imported blindResidual is used unchanged. For a proposed definition d, the measured reduction set is its intersection with the complement of the Setoid equality kernel of d. Thus the Lean definition is exactly the displayed P_Gamma formula and introduces no second residual or kernel.

The public hypotheses require the abstract real-valued set weight to be nonnegative and to be positive exactly on nonempty sets. Both requirements occur in the theorem type. The conclusion packages the defining equality, nonnegativity, and the equivalence between positive reduction weight and a blind residual pair separated by d.

Finite counting weight on Boolean state pairs supplies the positive example. A constant definition supplies the reverse example, and a zero weight shows that nonnegativity without strict nonempty-set detection is insufficient.

The closing catalog, language-closure, and target-usefulness maxim is not asserted as a Lean proposition: the source supplies no formal catalog, closure, or usefulness predicates from which a faithful statement could be formed.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelReductionMeasure.blind_kernel_reduction_measure`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction](BlindKernelObstruction.md)
