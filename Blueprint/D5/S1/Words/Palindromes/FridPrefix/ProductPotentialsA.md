# Compressed co-accessibility and product potentials

## Abstract

Compressed co-accessibility and product potentials

**Definition 1.1 (coreMasksA).**

$$coreMasksA:Array\left(Array\left(\mathbb{N}\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/ProductPotentialsA.coreMasksA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At (q,p), bit s of the stored natural number indicates co-accessibility of the triple (q,p,s). These are the literal masks tested by the product proof.

**Definition 1.2 (potentialDigitsA).**

$$potentialDigitsA:Array\left(Array\left(\mathbb{N}\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/FridPrefix/ProductPotentialsA.potentialDigitsA` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At (q,p), the three-bit digit starting at bit 3s encodes U(q,p,s)+2. The decoder performs a right shift followed by remainder modulo 8 and an integer subtraction of 2. The literal arrays are printed in Lean.

## References

- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ProductPotentialsA.coreMasksA`
- Truth anchor: `D5/S1/Words/Palindromes/FridPrefix/ProductPotentialsA.potentialDigitsA`
