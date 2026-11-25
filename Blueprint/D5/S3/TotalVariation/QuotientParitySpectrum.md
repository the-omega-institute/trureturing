# Realizing an affine parity law with vanishing moments

## Abstract

A quotient criterion for affine independent-bit laws with arbitrary signed moments.

**Theorem 1.1 (The fair subgroup and the shifted quotient characterize the law).**

Lean statement: `D5/S3/TotalVariation/QuotientParitySpectrum.affine_law_iff_quotient_criterion`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/QuotientParitySpectrum.affine_law_iff_quotient_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let A be a finite additive commutative group with x+x=0 for every x. Let p be a real mass function on A of total mass one. The law p equals the output of an affine sum of finitely many independent bits, with all bias factors in the closed interval from -1 to 1, exactly when there are a subgroup H and an offset s with the following properties.

Every character nontrivial on H has zero moment. Shift p by s and sum its masses over the cosets of H. Every sign moment of this quotient law is strictly positive. At each nonzero quotient column, the product of the moments of the characters equal to -1 on that column is at most the product for the characters equal to +1.

For an existing representation, span the columns of the fair bits to form H and absorb the negative biases into the offset. For the converse, realize the shifted quotient law using the positive-spectrum criterion and lift its columns. Adding fair bits on H makes all moments outside its annihilator vanish. The translated law then has the required moments at every character, which determines every mass.

## References

- Truth anchor: `D5/S3/TotalVariation/QuotientParitySpectrum.affine_law_iff_quotient_criterion`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](../Entropy/Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/TotalVariation/PositiveParitySpectrum](PositiveParitySpectrum.md)
