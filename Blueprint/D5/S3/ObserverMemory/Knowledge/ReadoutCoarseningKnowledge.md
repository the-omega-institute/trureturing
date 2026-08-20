# Readout Coarsening and Knowledge

## Abstract

Coarsening a readout contravariantly shrinks its complex knowledge space.

**Theorem 1.1 (Readout coarsening shrinks knowledge).**

$$\forall X, Y_{0}, Y_{1}: \operatorname{Type},\ q_{0}: X \to Y_{0}, q_{1}: X \to Y_{1},\ r: Y_{0} \to Y_{1},\ q_{1} = r \circ q_{0} \Rightarrow\ K(q_{1}) \subseteq K(q_{0}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Knowledge/ReadoutCoarseningKnowledge.readout_coarsening_shrinks_knowledge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a readout q on a world type X, the imported knowledge space is the range of the linear pullback from complex observables on realized readout classes. It therefore constructs the source set of complex functions that factor through q.

The exact repository membership theorem identifies that pullback range with Mathlib's FactorsThrough predicate. If q1 is forget composed with q0, equality on a q0 fiber implies equality on the corresponding q1 fiber, so every q1-known observable is q0-known.

The proof applies mem_knowledgeSpace_iff_factorsThrough in both directions. Repository and pinned-Mathlib searches also checked the timed same-codomain knowledge theorem, factorsThrough_iff, extend_comp, comp_left, and comp_right; none directly states the displayed general inclusion.

## References

- Truth anchor: `D5/S3/ObserverMemory/Knowledge/ReadoutCoarseningKnowledge.readout_coarsening_shrinks_knowledge`
- Dependency: [D5/S3/ObserverMemory/Knowledge/FiniteCapacity](FiniteCapacity.md)
