# Measurable Total Variation Triangle

## Abstract

Truncated-difference suprema give measurable total variation its triangle and symmetry laws.

The quantity measurableTotalVariation mu nu is the supremum over measurable events of the larger of the two truncated differences of the measures on that event. It lives in the frozen module MeasurablePostprocessingDefectContraction, imported here. The formulas below abbreviate this quantity as mTV.

The general lemma carries the whole argument. iSup_max_tsub_triangle mentions no measure and no measurable structure: it is the order theory of truncated subtraction over an arbitrary index. The measure statement is its event-indexed instance, proved in one line.

An earlier draft stated only the measure version and argued in its own prose that the general form could not be given without introducing a second definition of the quantity. A review seat showed that argument was wrong: the general lemma can be stated inline over Index -> ENNReal, redefining nothing. It is now the primary theorem.

The demand for the triangle law comes from two frozen modules, Estimation/DataProcessing/MeasurableDescentErrorBounds and Estimation/SequentialDecisionRisk/MeasurableDeficiencyTriangle. Each privately proves the same unrestricted proposition: the same statement, proved twice. Their strategies are near-identical, but they are not literally the same proof text.

Both modules are frozen, so they cannot import this module, and this change removes none of their private copies. This module has zero consumers today. It does not promise to prevent a future copy.

Name-shaped search also misses relevant prior art. The public theorem D5/S3/TotalVariation/Metric.total_variation_triangle treats finite total variation of real vectors. The same module publicly names total_variation_eq_sup_event_gap for its event-supremum characterization, the closest concept hit. MeasurableDeficiencyTriangle publicly names a deficiency triangle while keeping this measurable-total-variation triangle private.

None of that prior art subsumes this theorem. The first two results are stated for a Fintype and real-valued functions, and the event-supremum one additionally assumes equal total mass, whereas this result admits arbitrary, possibly infinite measures.

Pinned Mathlib was searched by name and by concept. The relative used by the proof is tsub_le_tsub_add_tsub. The search found no upstream statement of this triangle law; that reports the search result and does not say that no upstream form can exist.

The repository also re-derives symmetry twice: once as a private named theorem in MeasurableDescentErrorBounds, and once inline, as the same simp call, inside a calculation in MeasurableDeficiencyTriangle. An earlier draft counted only declaration names, found one occurrence, and excluded symmetry on that basis. A review seat found the inline occurrence. Counting names undercounts duplication.

The value is API, not mathematical novelty. The general lemma proves an order-theoretic bound at a fixed index and lifts it to the suprema. The measure theorem is a single instantiation. Symmetry is one simp call.

**Theorem 1.1 (Indexed truncated differences satisfy the triangle bound).**

$$\begin{aligned}\forall Index: Type,\\\forall f, g, h: Index \to ENNReal,\\\operatorname{sup}_{i: Index} \max(tsub\left(f\left(i\right), h\left(i\right)\right), tsub\left(h\left(i\right), f\left(i\right)\right)) \leq \operatorname{sup}_{i: Index} \max(tsub\left(f\left(i\right), g\left(i\right)\right), tsub\left(g\left(i\right), f\left(i\right)\right)) + \operatorname{sup}_{i: Index} \max(tsub\left(g\left(i\right), h\left(i\right)\right), tsub\left(h\left(i\right), g\left(i\right)\right)).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle.iSup_max_tsub_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Index is an arbitrary type, with no Fintype or measurable structure. The three functions f, g, and h are arbitrary ENNReal-valued families, and there are no hypotheses. At each index, the two directed truncated differences are bounded through g; each term is then lifted to its corresponding supremum.

**Theorem 1.2 (Measurable total variation satisfies the triangle inequality).**

$$\begin{aligned}\forall A: Type, [MeasurableSpace\left(A\right)],\\\forall mu, nu, rho: Measure\left(A\right),\\mTV\left(mu, rho\right) \leq mTV\left(mu, nu\right) + mTV\left(nu, rho\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle.measurable_total_variation_triangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any measurable space and any three measures mu, nu, and rho, with no finiteness, probability-normalisation, or other hypotheses, this is the general lemma instantiated on measurable events.

**Theorem 1.3 (Measurable total variation is symmetric).**

$$\begin{aligned}\forall A: Type, [MeasurableSpace\left(A\right)],\\\forall mu, nu: Measure\left(A\right),\\mTV\left(mu, nu\right) = mTV\left(nu, mu\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle.measurable_total_variation_comm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any measurable space and any two measures mu and nu, with no hypotheses, exchanging the directed truncated differences leaves their maximum and hence mTV unchanged. The proof is one simp call.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle.iSup_max_tsub_triangle`
- Truth anchor: `D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle.measurable_total_variation_comm`
- Truth anchor: `D5/S3/Estimation/DataProcessing/MeasurableTotalVariationTriangle.measurable_total_variation_triangle`
- Dependency: [D5/S3/Estimation/DataProcessing/MeasurablePostprocessingDefectContraction](MeasurablePostprocessingDefectContraction.md)
