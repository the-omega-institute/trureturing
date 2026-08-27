# Observer Refinement, Visibility, and Residuals

## Abstract

Physical observer refinement is dual to visible and residual subspace inclusion.

**Theorem 1.1 (Observer refinement has dual visible and residual criteria).**

$$\begin{aligned}\forall d: Nat, \operatorname{NeZero}\left(d\right), IndexOne, IndexTwo: \operatorname{Type},\\effectsOne: IndexOne \to \operatorname{HermitianSpace}\left(d\right), effectsTwo: IndexTwo \to \operatorname{HermitianSpace}\left(d\right),\\\operatorname{let} stateOperator: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right) \to \operatorname{HermitianSpace}\left(d\right) := \rho \mapsto \operatorname{HermitianMk}\left(\operatorname{ofMatrixSymm}\left(\operatorname{val}\left(\rho\right)\right)\right),\\\operatorname{let} signatureOne := \rho \mapsto i \mapsto \operatorname{innerR}\left(\operatorname{stateOperator}\left(\rho\right), \operatorname{effectsOne}\left(i\right)\right),\\\operatorname{let} signatureTwo := \rho \mapsto i \mapsto \operatorname{innerR}\left(\operatorname{stateOperator}\left(\rho\right), \operatorname{effectsTwo}\left(i\right)\right),\\\operatorname{let} visibleOne := \operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), \operatorname{range}\left(effectsOne\right)\right)\right), visibleTwo := \operatorname{span}\left(\mathbb{R}, \operatorname{insert}\left(\operatorname{identityHermitian}\left(d\right), \operatorname{range}\left(effectsTwo\right)\right)\right),\\\operatorname{let} residualOne := \operatorname{orthogonal}\left(visibleOne\right), residualTwo := \operatorname{orthogonal}\left(visibleTwo\right),\\\operatorname{let} refines := \forall \rho, \sigma: \operatorname{DensityState}\left(\operatorname{Fin}\left(d\right)\right), \operatorname{signatureTwo}\left(\rho\right) = \operatorname{signatureTwo}\left(\sigma\right) \Rightarrow \operatorname{signatureOne}\left(\rho\right) = \operatorname{signatureOne}\left(\sigma\right),\\(refines \iff residualTwo \subseteq residualOne) \land \\(residualTwo \subseteq residualOne \iff visibleOne \subseteq visibleTwo).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurement/ObserverRefinementVisibleResidualEquivalence.observer_refinement_visible_residual_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each observer signature is constructed from real Hilbert--Schmidt pairings between density-state matrices and its Hermitian effect family. Its visible space is the real span of the identity and those effects, and its residual is the orthogonal complement of that span.

Refinement means that equality of the second observer's signature on two physical density states forces equality of the first. Perturbations around the maximally mixed state turn every residual direction into a difference of density states.

Consequently refinement is exactly reverse inclusion of residuals. The pinned orthogonal-complement order theorem then identifies that condition with forward inclusion of visible spaces.

## References

- Truth anchor: `D5/S3/Quantum/Measurement/ObserverRefinementVisibleResidualEquivalence.observer_refinement_visible_residual_equivalence`
- Dependency: [D5/S3/Quantum/Tomography/InformationalCompletenessEquivalence](../Tomography/InformationalCompletenessEquivalence.md)
