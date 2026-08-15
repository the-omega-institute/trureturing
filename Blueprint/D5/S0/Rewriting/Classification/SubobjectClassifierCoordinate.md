# Subobject Classifier Coordinates

## Abstract

A subobject classifier bijectively coordinates subobjects by characteristic morphisms.

**Theorem 1.1 (Characteristic morphisms bijectively coordinate subobjects).**

$$\forall classifier: \operatorname{SubobjectClassifier}(C), \forall X\in C,\ \operatorname{Bijective}((characteristic: \operatorname{Hom}(X, \omega_{classifier})) \mapsto \operatorname{pullback}(characteristic, \operatorname{truth}_{classifier})).$$

*Proof.* Machine-checked in Lean as `D5/S0/Rewriting/Classification/SubobjectClassifierCoordinate.subobject_classifier_coordinate_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a category with pullbacks and a chosen subobject classifier, pulling back the truth subobject along a morphism from X into Omega produces a subobject of X. The map is bijective, so every subobject has one characteristic morphism and distinct subobjects receive distinct coordinates.

Pinned Mathlib already packages this map as the homEquiv field of Subobject.Classifier.representableBy. The Lean theorem applies that exact equivalence's bundled bijectivity result; it does not reprove the representability theorem or introduce a competing notion of classification.

## References

- Truth anchor: `D5/S0/Rewriting/Classification/SubobjectClassifierCoordinate.subobject_classifier_coordinate_bijection`
