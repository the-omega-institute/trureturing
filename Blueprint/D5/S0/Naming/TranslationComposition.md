# Composition of Approximate Translations

## Abstract

Semantically composable approximate translations add error and compose resources.

**Definition 1.1 (Partial resource-controlled translation).**

Lean statement: `D5/S0/Naming/TranslationComposition.Translation`

*Formalization.* `D5/S0/Naming/TranslationComposition.Translation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A translation carries a partial name map, an isometric embedding between meaning spaces, a conditional semantic-error bound, and a monotone natural-valued resource modulus. The semantic bound is required exactly when the source and target partial assignments both have values.

**Definition 1.2 (Semantic composability).**

Lean statement: `D5/S0/Naming/TranslationComposition.SemanticallyComposable`

*Formalization.* `D5/S0/Naming/TranslationComposition.SemanticallyComposable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At every point of the ordinary composite map domain whose two endpoint meanings exist, semantic composability requires the intermediate meaning to exist as well. This makes the source phrase composition is defined precise for partial semantic assignments; without it, both component semantic bounds could hold vacuously while the composite bound fails.

**Theorem 1.3 (Translation composition adds tolerance).**

$$\operatorname{tolerance}\left(\operatorname{compose}\left(\mathit{translation2}, \mathit{translation1}\right)\right) = \mathit{epsilon1} + \mathit{epsilon2}$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/TranslationComposition.translation_composition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two semantically composable translations admit a translation on the standard composite domain. Its name map and isometric embedding are the corresponding function composites, its tolerance is epsilon1 plus epsilon2, and its resource modulus is modulus2 composed with modulus1. The semantic estimate is the metric triangle inequality with the second embedding's distance preservation; the resource estimate uses monotonicity.

## References

- Truth anchor: `D5/S0/Naming/TranslationComposition.SemanticallyComposable`
- Truth anchor: `D5/S0/Naming/TranslationComposition.Translation`
- Truth anchor: `D5/S0/Naming/TranslationComposition.translation_composition`
- Dependency: [D5/S0/Naming/NamingSystem](NamingSystem.md)
