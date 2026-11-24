# Layer Shift Is Natural

## Abstract

A layer-shift natural transformation commutes with every lifting morphism.

**Theorem 1.1 (Layer shift commutes with lifting morphisms).**

$$shift_{Y} \circ Current(f) = Shifted(f) \circ shift_{X}$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/LayerShiftNaturality.layer_shift_naturality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the objects and morphisms of a category encode one layer's objects and their lifting maps. A current-layer interpretation and a shifted-layer interpretation are connected by a natural transformation. For every lifting morphism, the theorem states that applying the current interpretation and then shifting is equal to shifting first and applying the shifted interpretation. Thus the layer shift is independent of which endpoint of the lifting map is used to compute the comparison.

The category operations satisfy the identity and associativity laws, and both interpretations preserve identities and composition. The transformation supplies the commuting-square law for every morphism. The proof applies that law to the given lifting map.

## References

- Truth anchor: `D5/S0/Computability/LayerShiftNaturality.layer_shift_naturality`
