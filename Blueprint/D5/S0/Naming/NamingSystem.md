# Countable Naming Systems

## Abstract

Finite height layers make partial naming systems countable, leaving a null named image.

**Definition 1.1 (Partial naming system with finite height layers).**

Lean statement: `D5/S0/Naming/NamingSystem.NamingSystem`

*Formalization.* `D5/S0/Naming/NamingSystem.NamingSystem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A naming system over a measured carrier X consists of a name type N, a partial assignment from N to X represented by an Option-valued map, a natural-valued height, and a proof that every bounded height layer is finite. Uncountability and measure hypotheses are theorem assumptions rather than fields tied to a special carrier.

**Lemma 1.2 (Finite height layers make the name type countable).**

$$\operatorname{Countable}\left(N\right)$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/NamingSystem.name_layer_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every name lies in the layer indexed by its own height. The name type is therefore a countable union of finite sublevels, so it is countable.

**Theorem 1.3 (Countable naming families have null named image).**

$$\operatorname{mu}\left(\operatorname{namedUnion}\left(\mathit{systems}\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S0/Naming/NamingSystem.dark_side_conservation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a countable family of naming systems on an uncountable carrier with an atomless sigma-finite measure, the union of all points reached by their partial assignments has measure zero. Equivalently, the dark side, its complement, has full measure in complement-null form. The repository proof derives countability through the NamingSystem height layers and delegates the final measure step directly to mathlib's Set.Countable.measure_zero theorem.

## References

- Truth anchor: `D5/S0/Naming/NamingSystem.NamingSystem`
- Truth anchor: `D5/S0/Naming/NamingSystem.dark_side_conservation`
- Truth anchor: `D5/S0/Naming/NamingSystem.name_layer_finite`
