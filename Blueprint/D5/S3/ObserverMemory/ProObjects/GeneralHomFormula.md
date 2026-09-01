# The General Pro-Object Hom Formula

## Abstract

Morphisms between presented pro-objects form a limit of stage-map colimits.

**Theorem 1.1 (Morphisms are a limit of stage-map colimits).**

$$\operatorname{Hom}_{\operatorname{ProObjectCategory}(C)}(\operatorname{presentedObject}(X), \operatorname{presentedObject}(Y)) \equiv \operatorname{lim}_{j} \operatorname{colim}_{i} \operatorname{Hom}_{C}(X_{i}, Y_{j}).$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/ProObjects/GeneralHomFormula.pro_category_hom_formula` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let I and J be small filtered categories. Diagrams X : I^op -> C and Y : J^op -> C present cofiltered pro-objects. For each target stage Y_j, source refinement gives the filtered colimit of the ordinary morphism types X_i -> Y_j.

These colimits vary contravariantly with the target stages. Their limit therefore records precisely the compatible target-stage classes, and is canonically equivalent to the morphism type between the two presented pro-objects.

Every target component has a representative at one sufficiently refined source stage. When both index categories have one object, the two universal constructions reduce to the ordinary Hom type; in Type, the identity function supplies an explicit inhabitant.

The Lean construction reuses the repository pro-object category and the pinned Mathlib Ind inclusion, its fully faithful Hom equivalence, pointwise colimit preservation, and the colimit-Yoneda Hom equivalence.

## References

- Truth anchor: `D5/S3/ObserverMemory/ProObjects/GeneralHomFormula.pro_category_hom_formula`
- Dependency: [D5/S3/ObserverMemory/ProObjects/ConceptAnchorHomAsymmetry](ConceptAnchorHomAsymmetry.md)
