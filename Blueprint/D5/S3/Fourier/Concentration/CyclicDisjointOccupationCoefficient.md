# Cyclic frequency bands for disjoint occupations

## Abstract

Character projection retains the two occupation degrees and the cyclic frequency gap.

**Theorem 1.1 (The mixed coefficient after character projection).**

$$qM_{R} = (d!)^{2} \sum_{k \in \operatorname{ZMod}\left(q\right)}Q_{k}[d,d] \sum_{r \in R}X_{k}(r)$$

*Proof.* Machine-checked in Lean as `D5/S3/Fourier/Concentration/CyclicDisjointOccupationCoefficient.cyclic_disjoint_band_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let q be positive. Each index j has a residue a(j) modulo q and a real weight w(j). For degree d and a set R of residues, M with subscript R is the weighted mass of ordered pairs of disjoint degree-d occupations whose first frequency sum minus the second belongs to R.

For each k modulo q, the local polynomial has constant coefficient one. For n from one to d, it assigns w(j)^n/n! to degree (n,0) with the negative character at n a(j), and to degree (0,n) with the positive character at n a(j). Write X with subscript k for the positive character. The product of those local polynomials is Q with subscript k. It has mixed coefficient Q(k)[d,d].

First expand a product in the additive monoid carrying the left degree, right degree and residue. The (d,d,r) coefficient groups all pairs with the two specified degrees and residue r. Multiplying by the square of d factorial gives the original multinomial weights. Applying a character to each residue commutes with convolution, leaving only the degree coordinates. Fourier inversion recovers the sum over R.

## References

- Truth anchor: `D5/S3/Fourier/Concentration/CyclicDisjointOccupationCoefficient.cyclic_disjoint_band_product`
- Dependency: [D5/S3/Fourier/Concentration/DisjointSupportOccupationMass](DisjointSupportOccupationMass.md)
