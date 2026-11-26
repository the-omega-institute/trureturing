# Conjugating the swaps of a coordinate star

## Abstract

A single cube translation turns independently complemented star swaps into coordinate transpositions.

**Definition 1.1 (Translation of a cube vertex).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.translate`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.translate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Translation by t adds t by coordinatewise XOR.

**Theorem 1.2 (Cube translations are involutions).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.translate_involutive`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.translate_involutive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the same translation twice adds each bit twice and returns the starting vertex.

**Definition 1.3 (A swap with optional complementation).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.chosenSwap`

*Formalization.* `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.chosenSwap` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On distinct coordinates r and j, the map exchanges their bits and XORs both with the same chosen bit. It fixes the other coordinates.

**Theorem 1.4 (One translation conjugates all the chosen star swaps).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.exists_translation_conjugating_star_swaps`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.exists_translation_conjugating_star_swaps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a coordinate r and choose a complementation bit independently for each transposition of r and j. Set the translation bit at r to false and the bit at j to that choice. Applying the chosen swap after this translation equals applying the ordinary swap before the translation. Since translation is an involution, the identity gives simultaneous conjugation on the whole coordinate star.

**Theorem 1.5 (The translated function is invariant under coordinate permutations).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.exists_translation_perm_invariant_of_no_split`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.exists_translation_perm_invariant_of_no_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each j distinct from r, suppose double flipping r and j preserves the function either on all vertices with unequal bits at r and j or on all vertices with equal bits there. The unequal-bit hypothesis gives invariance under the ordinary swap, and the equal-bit hypothesis gives invariance under the complemented swap. Each choice acts as the identity on the other class.

Conjugate the chosen swaps by one translation with its r bit false. The ordinary star transpositions generate every coordinate permutation, since a transposition between two leaves is a product of three star transpositions. Thus the translated function is invariant under precomposition by every coordinate permutation. The codomain can be any type.

**Theorem 1.6 (The translated function is constant on each Hamming layer).**

Lean statement: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.exists_translation_hamming_layer_constant`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.exists_translation_hamming_layer_constant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same star hypothesis, there is a translation whose r bit is false and after which the function has equal values at every pair of vertices of the same Hamming weight. A coordinate permutation sends one such vertex to the other by matching their true-coordinate sets and matching their complements.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.chosenSwap`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.exists_translation_conjugating_star_swaps`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.exists_translation_hamming_layer_constant`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.exists_translation_perm_invariant_of_no_split`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.translate`
- Truth anchor: `D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSwapConjugation.translate_involutive`
- Dependency: [D5/S3/Combinatorics/Graph/HypercubeCritical/BalancedCriticalSpectrum](../BalancedCriticalSpectrum.md)
