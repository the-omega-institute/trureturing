# Factor Image Stability

## Abstract

Surjective semiconjugacies preserve finite iterate-image bounds and stabilization.

**Theorem 1.1 (Factor maps preserve iterate images and stabilization).**

$$\forall Y, Z, [\operatorname{Finite} Y],\ sourceStep: Y \to Y,\ factorStep: Z \to Z,\ quotientMap: Y \to Z,\ \operatorname{Surjective}(quotientMap) \land \operatorname{Semiconj}(quotientMap, sourceStep, factorStep) \Rightarrow \forall k\in \mathbb{N},\ \operatorname{image}(quotientMap, \operatorname{range}(sourceStep^{k})) = \operatorname{range}(factorStep^{k}) \land\ \operatorname{ncard}(\operatorname{range}(factorStep^{k})) \leq \operatorname{ncard}(\operatorname{range}(sourceStep^{k})) \land\ (\operatorname{range}(sourceStep^{k}) = \operatorname{range}(sourceStep^{k + 1}) \Rightarrow \operatorname{range}(factorStep^{k}) = \operatorname{range}(factorStep^{k + 1})).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/InverseLimits/FactorImageStability.surjective_semiconj_iterate_ranges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let quotientMap be a surjection from a finite source carrier Y onto Z, semiconjugating sourceStep to factorStep. At every time k, its image of the source iterate range is exactly the factor iterate range.

Consequently the factor range has at most as many states as the source range. If the source image chain is already stable between k and k+1, applying quotientMap shows that the factor image chain is stable at the same step.

This closes theorem/8.6 from qdo-v1: factor coarse-graining does not increase transient image depth. The statement records the iterate image equality, its finite-cardinality consequence, and the stabilization implication.

Pinned Mathlib supplied Function.Semiconj.iterate_right, Set.range_comp, Function.Surjective.range_comp, and Set.ncard_image_le. Repository and pinned-source searches found no full theorem. Loogle returned zero hits; LeanSearch's API returned HTTP 404 and supplied no search conclusion.

## References

- Truth anchor: `D5/S3/ObserverMemory/InverseLimits/FactorImageStability.surjective_semiconj_iterate_ranges`
