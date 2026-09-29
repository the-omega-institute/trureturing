# Prime Collinear Triple Census

## Abstract

Prime-modulus census of admissible collinear triples.

**Theorem 1.1 (Exact count over a prime residue field).**

$$\operatorname{Prime}\left(p\right) \implies \operatorname{card}\left(\operatorname{Triple}\left(p\right)\right) = p \times (p - 1) \times \operatorname{choose}\left(p, 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Collinear/PrimeCollinearTripleCensus.card_triples_prime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An admissible triple is an unordered three-point set with distinct first and second coordinates and zero difference determinant. Over the field of residues modulo a prime p, two points determine a unique affine line. The determinant condition places the third point on it, and distinct second coordinates force a nonzero slope. Conversely, a nonzero slope, an intercept, and a three-element set of first coordinates determine exactly one admissible triple. Counting these choices gives the formula, including the empty case p=2 and the case p=3.

## References

- Truth anchor: `D5/S3/Factorization/Collinear/PrimeCollinearTripleCensus.card_triples_prime`
- Dependency: [D5/S3/Factorization/CollinearTripleTranslationOrbits](../CollinearTripleTranslationOrbits.md)
