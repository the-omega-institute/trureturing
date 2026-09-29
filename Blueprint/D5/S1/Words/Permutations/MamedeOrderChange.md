# Order Change and Pair Crossing

## Abstract

A change in the order of two values has a crossing generator.

Relative order is measured by the inverse permutation, so it compares the positions occupied by two values rather than their values.

**Definition 1.1 (Relative order).**

$$\operatorname {before}\left(sigma, x, y\right) \iff \operatorname {positionOf}\left(sigma, x\right) < \operatorname {positionOf}\left(sigma, y\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeOrderChange.before` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse image of x has smaller Fin value than the inverse image of y.

**Definition 1.2 (Pair crossing).**

$$\operatorname {crossing}\left(sigma, k, x, y\right) \iff \operatorname {occupyAdjacent}\left(sigma, k, x, y\right) \lor \operatorname {occupyAdjacent}\left(sigma, k, y, x\right)$$

*Formalization.* `D5/S1/Words/Permutations/MamedeOrderChange.crossing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The values x and y occupy the two positions swapped by generator k, in either order.

**Theorem 1.3 (A reversal has a crossing).**

$$\operatorname {Valid}\left(n, w\right) \land x \neq y \land \operatorname {before}\left(sigma, x, y\right) \neq \operatorname {before}\left(sigma \times \operatorname {prod}\left(n, w\right), x, y\right) \implies \exists p , \exists k , \exists q , w = \operatorname {concat}\left(p, k, q\right) \land \operatorname {crossing}\left(sigma \times \operatorname {prod}\left(n, p\right), k, x, y\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Permutations/MamedeOrderChange.order_change_has_crossing` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every valid adjacent-swap word, a change in pair order occurs at an actual letter of that word and its preceding prefix product.

## References

- Truth anchor: `D5/S1/Words/Permutations/MamedeOrderChange.before`
- Truth anchor: `D5/S1/Words/Permutations/MamedeOrderChange.crossing`
- Truth anchor: `D5/S1/Words/Permutations/MamedeOrderChange.order_change_has_crossing`
- Dependency: [D5/S1/Words/Permutations/MamedeAdjacentWords](MamedeAdjacentWords.md)
