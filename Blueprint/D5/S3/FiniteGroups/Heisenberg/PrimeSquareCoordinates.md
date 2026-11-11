# Prime-square residues and dual numbers

## Abstract

Prime-square residues and dual numbers have compatible complete residue-coordinate interfaces.

**Definition 1.1 (Two residue digits).**

$$\forall p \in \mathbb{N},\; (\operatorname{NatPrime}\left(p\right)) \Rightarrow (\forall x \in \operatorname{ZMod}\left(\operatorname{mul}\left(p, p\right)\right),\; \operatorname{squareCode}\left(p, x\right) = \operatorname{pair}\left(\operatorname{Residue}\left(p, \operatorname{val}\left(x\right)\right), \operatorname{Residue}\left(p, \operatorname{NatDiv}\left(\operatorname{val}\left(x\right), p\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/Heisenberg/PrimeSquareCoordinates.squareCode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural prime p, squareCode is an equivalence from ZMod(p*p) to ZMod p times ZMod p. It sends x to its residue x.val modulo p and the residue of the natural quotient x.val/p. Its inverse sends (a,b) to a.val+p*b.val modulo p*p. The canonical representatives of a and b lie below p, so their combined value lies below p*p. The division algorithm proves both inverse laws. Here val denotes the canonical nonnegative representative, and the slash inside NatDiv denotes natural division.

**Definition 1.2 (The integer-residue coordinates).**

$$\forall p \in \mathbb{N},\; (\operatorname{NatPrime}\left(p\right)) \Rightarrow (\operatorname{HasType}\left(\operatorname{squareCoordinates}\left(p\right), \operatorname{ResidueCoordinates}\left(\operatorname{ZMod}\left(\operatorname{mul}\left(p, p\right)\right), \operatorname{ZMod}\left(p\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/Heisenberg/PrimeSquareCoordinates.squareCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The residue map is the canonical ring homomorphism from ZMod(p*p) to ZMod p. A ring element is a unit exactly when its representative is not divisible by p, equivalently its residue is nonzero. The kernel embedding j(a) is p*a.val modulo p*p. Multiplication gives j(a)*x=j(a*res(x)): changing the integer product by a multiple of p does not affect its product with p modulo p*p. Thus the complete ResidueCoordinates interface, including the nilpotent multiplication law, is proved for this ring.

**Definition 1.3 (The dual-number coordinates).**

$$\forall p \in \mathbb{N},\; (\operatorname{NatPrime}\left(p\right)) \Rightarrow (\operatorname{HasType}\left(\operatorname{dualCoordinates}\left(p\right), \operatorname{ResidueCoordinates}\left(\operatorname{DualNumber}\left(\operatorname{ZMod}\left(p\right)\right), \operatorname{ZMod}\left(p\right)\right)\right))$$

*Formalization.* `D5/S3/FiniteGroups/Heisenberg/PrimeSquareCoordinates.dualCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A dual number is a pair (a,b), with product (a,b)(c,d)=(ac,ad+bc). The coordinate equivalence is the identity on this product type, res is its first projection, and j(b)=(0,b). Mathlib's unit criterion says that a dual number is a unit exactly when its first coordinate is a unit in the field. Direct coordinate multiplication proves the nilpotent law. Every natural prime, including two, is admitted.

## References

- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/PrimeSquareCoordinates.dualCoordinates`
- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/PrimeSquareCoordinates.squareCode`
- Truth anchor: `D5/S3/FiniteGroups/Heisenberg/PrimeSquareCoordinates.squareCoordinates`
- Dependency: [D5/S3/FiniteGroups/Heisenberg/DeterminantCharts](DeterminantCharts.md)
