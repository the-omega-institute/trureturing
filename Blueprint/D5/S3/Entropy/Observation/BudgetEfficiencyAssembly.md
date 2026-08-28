# Budget and Efficiency Assembly

## Abstract

Refinement information, innovation counts, and finite closure-spectrum memory budgets are assembled on the canonical finite carriers.

**Theorem 1.1 (Refinement gain, innovation budget, and closure-spectrum telescope).**

$$\begin{aligned}\forall P, F, X, Q: \operatorname{Type},\\C: \mathbb{N} \to \operatorname{Type}, [\operatorname{Fintype}(P)] [\operatorname{Fintype}(F)] [\operatorname{Fintype}(X)],\\fintypeC: \forall n: \mathbb{N}, [\operatorname{Fintype}(\operatorname{C}(n))],\\p: \operatorname{Prod}(P, F) \to \mathbb{R}, hp: (\forall z: \operatorname{Prod}(P, F), 0 \leq \operatorname{p}(z)) \land \sum_{z} \operatorname{p}(z) = 1,\\q: \forall n: \mathbb{N}, P \to \operatorname{C}(n), forget: \forall n: \mathbb{N}, \operatorname{C}(n+1) \to \operatorname{C}(n),\\hrefine: \forall n: \mathbb{N}, \operatorname{q}(n) = \operatorname{comp}(\operatorname{forget}(n), \operatorname{q}(n+1)), update: X \to X, readout: X \to Q\Rightarrow\\mass: P \to \mathbb{R} = \operatorname{marginal}(p),\\{}h: \mathbb{N} \to \mathbb{R} = fun n\mapsto \operatorname{conditionalEntropy}(\operatorname{completionLaw}(mass, \operatorname{q}(n), \operatorname{q}(n+1))),\\{}g: \mathbb{N} \to \mathbb{R} = fun n\mapsto \operatorname{refinementGain}(p, \operatorname{q}(n+1), \operatorname{forget}(n)),\\{}eta: \mathbb{N} \to \mathbb{R} = fun n\mapsto \operatorname{if}(\operatorname{h}(n) = 0, 0, \operatorname{g}(n) / \operatorname{h}(n)),\\{}(\forall n: \mathbb{N}, (0 \leq \operatorname{g}(n) \land \operatorname{g}(n) \leq \operatorname{h}(n) \land (0 < \operatorname{h}(n)\Rightarrow \operatorname{eta}(n) = \operatorname{g}(n) / \operatorname{h}(n)) \land (\operatorname{h}(n) = 0\Rightarrow \operatorname{eta}(n) = 0))) \land (\operatorname{Summable}(h) \land \sum_{n}^{\infty} \operatorname{h}(n) \leq H(mass) \land \forall epsilon: \mathbb{R}, (0 < epsilon\Rightarrow \operatorname{ncard}(\{n\in \mathbb{N} \mid epsilon \leq \operatorname{h}(n)\}) \leq H(mass) / epsilon)) \land (\sum_{k\in\operatorname{range}(\operatorname{observationStabilityDepth}(update, readout))} {\operatorname{log}(\operatorname{observationClassCount}(update, readout, k+1)) - \operatorname{log}(\operatorname{observationClassCount}(update, readout, k))} = \operatorname{log}(\operatorname{infiniteObservationClassCount}(update, readout)) - \operatorname{log}(\operatorname{Nat}.card(\operatorname{Set}.range(readout)))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/BudgetEfficiencyAssembly.budget_efficiency_assembly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite past/future law and deterministic fine-to-coarse readout use the canonical predictive-memory and refinement-gain definitions. The first conjunct is the imported exact decomposition and its nonnegativity.

A nonnegative summable innovation sequence with a total budget H obeys the canonical threshold-count bound. The final conjunct applies the finite observation quotient and complete-future quotient to the closure-spectrum log telescope; the endpoint is the realized readout image, not an arbitrary codomain complement.

No new probability law, quotient, or resolution object is declared. The finite/infinite quotient bridge is proved locally from the existing future relations and the pinned quotient-range equivalence.

## References

- Truth anchor: `D5/S3/Entropy/Observation/BudgetEfficiencyAssembly.budget_efficiency_assembly`
- Dependency: [D5/S3/ConceptDynamics/Completion/CompletionInformationCost](../../ConceptDynamics/Completion/CompletionInformationCost.md)
- Dependency: [D5/S3/Entropy/EntropyNonneg](../EntropyNonneg.md)
- Dependency: [D5/S3/Entropy/Observation/ConditionalChoiceOutcomeChainRule](ConditionalChoiceOutcomeChainRule.md)
- Dependency: [D5/S3/Entropy/Submodularity/RefinementInformationDecomposition](../Submodularity/RefinementInformationDecomposition.md)
- Dependency: [D5/S3/Observer/Prediction/StableDepthCardinalityBounds](../../Observer/Prediction/StableDepthCardinalityBounds.md)
- Dependency: [D5/S3/Observer/Separation/FiniteHistoryStability](../../Observer/Separation/FiniteHistoryStability.md)
- Dependency: [D5/S3/Observer/Tomography/InnovationCountBound](../../Observer/Tomography/InnovationCountBound.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability](../../ObserverMemory/Prediction/ConditionalEntropyStability.md)
