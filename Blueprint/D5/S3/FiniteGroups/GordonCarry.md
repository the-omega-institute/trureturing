# Reversible mixed-radix carries

## Abstract

Odd radix predecessor carries retain the whole bounded digit tuple.

**Theorem 1.1 (Recovering the first nonzero digit).**

$$\forall ds \in \operatorname{List}\left(OddRadix\right),\; \operatorname{Injective}\left(\operatorname{carry}\left(ds\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GordonCarry.carry_injective` (`✓ std3`). ∎

*Citation.* Basil Gordon (1961). *Sequences in groups with distinct partial products*. DOI: [10.2140/pjm.1961.11.1309](https://doi.org/10.2140/pjm.1961.11.1309). URL: <https://msp.org/pjm/1961/11-4/p14.xhtml>.

*Commentary.*

Each radix is odd and greater than one. Box is the nested product of its cyclic residue groups, with the least significant digit first. The predecessor borrows recursively through zero digits. In the carry output, digits before the first nonzero input digit vanish, that digit becomes its negative double, and higher digits become their negative doubles minus one. Inverting doubling recovers every digit. Empty lists and repeated radices are included.

**Theorem 1.2 (Complete borrow and the zero fiber).**

$$\forall ds \in \operatorname{List}\left(OddRadix\right),\; \forall x \in \operatorname{Box}\left(ds\right),\; (\operatorname{carry}\left(ds, x\right) = 0) \Leftrightarrow (x = 0)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GordonCarry.carry_eq_zero` (`✓ std3`). ∎

*Citation.* Basil Gordon (1961). *Sequences in groups with distinct partial products*. DOI: [10.2140/pjm.1961.11.1309](https://doi.org/10.2140/pjm.1961.11.1309). URL: <https://msp.org/pjm/1961/11-4/p14.xhtml>.

*Commentary.*

A zero input borrows through every coordinate and produces zero. Injectivity proves the converse, including the empty tuple. This distinguishes an internal multiple of the odd radix product from any nonzero residue in the even-edge inventory.

**Theorem 1.3 (Digit complement reverses rank).**

$$\forall ds \in \operatorname{List}\left(OddRadix\right),\; \forall x \in \operatorname{Box}\left(ds\right),\; \operatorname{rank}\left(ds, x\right)+\operatorname{rank}\left(ds, -x-\operatorname{ones}\left(ds\right)\right)+1 = \operatorname{volume}\left(ds\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GordonCarry.rank_complement` (`✓ std3`). ∎

*Citation.* Basil Gordon (1961). *Sequences in groups with distinct partial products*. DOI: [10.2140/pjm.1961.11.1309](https://doi.org/10.2140/pjm.1961.11.1309). URL: <https://msp.org/pjm/1961/11-4/p14.xhtml>.

*Commentary.*

Rank is the bounded mixed-radix integer, not a group homomorphism. Coordinatewise complement sends rank r to the product of the radices minus one minus r. This is the arithmetic step that separates opposite-parity prefixes.

**Theorem 1.4 (Predecessor agrees with modular subtraction).**

$$\forall ds \in \operatorname{List}\left(OddRadix\right),\; \forall n \in \mathbb{N},\; (0 < n) \Rightarrow (\operatorname{pred}\left(ds, \operatorname{residue}\left(ds, n\right)\right) = \operatorname{residue}\left(ds, n-1\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/FiniteGroups/GordonCarry.pred_residue` (`✓ std3`). ∎

*Citation.* Basil Gordon (1961). *Sequences in groups with distinct partial products*. DOI: [10.2140/pjm.1961.11.1309](https://doi.org/10.2140/pjm.1961.11.1309). URL: <https://msp.org/pjm/1961/11-4/p14.xhtml>.

*Commentary.*

Residue reduces a natural index modulo the product and decodes its bounded digits. For every positive index, digit predecessor agrees with index subtraction by one. At a multiple of the product this is the full wrap to the maximal tuple.

## References

- Truth anchor: `D5/S3/FiniteGroups/GordonCarry.carry_eq_zero`
- Truth anchor: `D5/S3/FiniteGroups/GordonCarry.carry_injective`
- Truth anchor: `D5/S3/FiniteGroups/GordonCarry.pred_residue`
- Truth anchor: `D5/S3/FiniteGroups/GordonCarry.rank_complement`
