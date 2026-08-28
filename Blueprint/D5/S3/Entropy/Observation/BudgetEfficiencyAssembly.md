# Budget and Efficiency Assembly

## Abstract

Refinement information, innovation counts, and finite closure-spectrum memory budgets are assembled on the canonical finite carriers.

**Theorem 1.1 (Refinement gain, innovation budget, and closure-spectrum telescope).**

$$\begin{aligned}\forall P, F, Fine, Coarse, X, Q: \operatorname{Type},\\{}[\operatorname{Fintype}(P)] [\operatorname{Fintype}(F)] [\operatorname{Fintype}(Fine)] [\operatorname{Fintype}(Coarse)] [\operatorname{Fintype}(X)],\\p: \operatorname{Prod}(P, F) \to \mathbb{R}, (\forall z: \operatorname{Prod}(P, F), 0 \leq \operatorname{p}(z)) \land \sum_{z} \operatorname{p}(z) = 1 \Rightarrow\\fine: P \to Fine, forget: Fine \to Coarse,\\innovation: \mathbb{N} \to \mathbb{R}, H: \mathbb{R}, epsilon: \mathbb{R},\\(\forall k: \mathbb{N}, 0 \leq \operatorname{innovation}(k)) \land \operatorname{Summable}(innovation) \land \operatorname{tsum}(innovation) \leq H \land 0 < epsilon,\\update: X \to X, readout: X \to Q\Rightarrow\\(\operatorname{predictiveMemory}(p, \operatorname{comp}(forget, fine)) - \operatorname{predictiveMemory}(p, fine) = \operatorname{refinementGain}(p, fine, forget) \land 0 \leq \operatorname{refinementGain}(p, fine, forget)) \land (\operatorname{ncard}(\operatorname{thresholdSet}(epsilon, innovation)) \leq \operatorname{divide}(H, epsilon)) \land (\sum_{k\in\operatorname{range}(\operatorname{stabilityDepth}(update, readout))} \operatorname{logIncrement}(update, readout, k) = \operatorname{log}(\operatorname{completeClassCount}(update, readout)) - \operatorname{log}(\operatorname{readoutImageCard}(readout))).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/Observation/BudgetEfficiencyAssembly.budget_efficiency_assembly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite past/future law and deterministic fine-to-coarse readout use the canonical predictive-memory and refinement-gain definitions. The first conjunct is the imported exact decomposition and its nonnegativity.

A nonnegative summable innovation sequence with a total budget H obeys the canonical threshold-count bound. The final conjunct applies the finite observation quotient and complete-future quotient to the closure-spectrum log telescope; the endpoint is the realized readout image, not an arbitrary codomain complement.

No new probability law, quotient, or resolution object is declared. The finite/infinite quotient bridge is proved locally from the existing future relations and the pinned quotient-range equivalence.

## References

- Truth anchor: `D5/S3/Entropy/Observation/BudgetEfficiencyAssembly.budget_efficiency_assembly`
- Dependency: [D5/S3/Entropy/Submodularity/RefinementInformationDecomposition](../Submodularity/RefinementInformationDecomposition.md)
- Dependency: [D5/S3/Observer/Prediction/StableDepthCardinalityBounds](../../Observer/Prediction/StableDepthCardinalityBounds.md)
- Dependency: [D5/S3/Observer/Separation/FiniteHistoryStability](../../Observer/Separation/FiniteHistoryStability.md)
- Dependency: [D5/S3/Observer/Tomography/InnovationCountBound](../../Observer/Tomography/InnovationCountBound.md)
- Dependency: [D5/S3/ObserverMemory/Prediction/ConditionalEntropyStability](../../ObserverMemory/Prediction/ConditionalEntropyStability.md)
