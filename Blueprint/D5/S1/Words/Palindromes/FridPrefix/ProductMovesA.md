# The seventeen literal arrays store all 829 endpoint moves for six-bit chunks

## Abstract

The seventeen literal arrays store all 829 endpoint moves for six-bit chunks

**Definition 1.1 (movesA).**

$$movesA:Array\left(Array\left(tuple\left(\mathbb{N}, \mathbb{N}, \mathbb{N}\right)\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/ProductMovesA.movesA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The seventeen literal arrays store all 829 endpoint moves for six-bit chunks. Each triple is (first chunk, second chunk, endpoint destination). The checker verifies equality with movesFrom(q,6).

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ProductMovesA.movesA`
