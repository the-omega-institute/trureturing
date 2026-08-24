# Directly Provable DECT Laws

## Abstract

Nine direct DECT laws are packaged without duplicating canonical primitives.

**Theorem 1.1 (Nine direct laws for definition escape and completion).**

$$\operatorname{E}\left(\operatorname{join}\left(q, d\right), T\right) = \operatorname{intersection}\left(\operatorname{E}\left(q, T\right), \operatorname{ker}\left(d\right)\right),\\{}\operatorname{E}\left(q, T\right) = \emptyset \Leftrightarrow \operatorname{FactorsThrough}\left(T, q\right),\\{}\operatorname{Refines}\left(d, q\right) \Rightarrow \operatorname{E}\left(\operatorname{join}\left(q, d\right), T\right) = \operatorname{E}\left(q, T\right),\\{}\operatorname{Nonempty}\left(\operatorname{blindResidual}\left(Gamma, q, T\right)\right) \Rightarrow \neg\operatorname{finiteSelectionSufficient}\left(Gamma, q, T\right),\\{}(\operatorname{Finite}\left(X\right) \land \operatorname{blindResidual}\left(Gamma, q, T\right) = \emptyset) \Rightarrow \exists n, defs, \operatorname{E}\left(\operatorname{languageExtension}\left(q, defs\right), T\right) = \emptyset,\\{}(\operatorname{Measurable}\left(\operatorname{E}\left(q, T\right)\right) \land \operatorname{MeasurableCuts}\left(cut\right)) \Rightarrow \operatorname{mu}\left(\operatorname{captured}\left(\operatorname{union}\left(A, B\right)\right)\right) + \operatorname{mu}\left(\operatorname{captured}\left(\operatorname{intersection}\left(A, B\right)\right)\right) \leq \operatorname{mu}\left(\operatorname{captured}\left(A\right)\right) + \operatorname{mu}\left(\operatorname{captured}\left(B\right)\right),\\{}\operatorname{RightInverse}\left(prepare, projection\right) \Rightarrow \operatorname{preparedDefect}\left(update, prepare, X\right) = \operatorname{oneStepDefect}\left(update, X\right),\\{}(\operatorname{RightInverse}\left(prepare, projection\right) \land \operatorname{SemigroupLaw}\left(evolution\right)) \Rightarrow \operatorname{semigroupDefect}\left(t + s, m\right) = \operatorname{preparedDefectAfter}\left(t, s, m\right),\\{}(\operatorname{LipschitzWith}\left(K, second\right) \land \operatorname{dist}\left(\operatorname{first}\left(X\right), y\right) \leq delta \land \operatorname{dist}\left(\operatorname{second}\left(y\right), \operatorname{direct}\left(X\right)\right) \leq eta) \Rightarrow \operatorname{dist}\left(\operatorname{second}\left(\operatorname{first}\left(X\right)\right), \operatorname{direct}\left(X\right)\right) \leq K \times delta + eta.$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/DefinitionEscape/DirectlyProvableLaws.directly_provable_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nine conjuncts follow the source order exactly: residual intersection; sufficiency-factorization; zero gain from a redundant definition; blind-kernel impossibility; finite-object compactness; submodular capture; the prepared one-step defect identity; the semigroup defect identity; and the approximate cascade triangle bound.

The first conjunct applies residual_join_law. The second uses the same fiber-constancy equivalence packaged by target_recovery_criterion, including the empty-state case without adding an inhabitedness premise. The fourth applies blind_kernel_obstruction after its residual witness supplies an inhabited state.

The canonical defectRelation is the only target residual throughout. For finite X, each baseline defect pair is assigned a package definition that separates it; enumeration of the finite subtype then gives a finite sufficient extension. No second residual, kernel, or joint readout is introduced.

Capture is measured on the residual intersection with a finite union of cuts. Finite-union measurability, measure monotonicity, and the union-intersection measure identity yield submodularity. The last three conjuncts respectively unfold composition, apply the semigroup law, and combine a Lipschitz bound with the metric triangle inequality.

Boolean examples witness a nonempty residual, redundant zero gain, a blind obstruction, and finite closure by one identity definition. Counting measure gives a strict capture inequality. Coordinate swap on real pairs gives nonzero prepared and semigroup defects, and the real identity map attains the cascade bound.

## References

- Truth anchor: `D5/S3/ConceptDynamics/DefinitionEscape/DirectlyProvableLaws.directly_provable_laws`
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelObstruction](BlindKernelObstruction.md)
- Dependency: [D5/S3/ConceptDynamics/DefinitionEscape/ResidualJoinLaw](ResidualJoinLaw.md)
