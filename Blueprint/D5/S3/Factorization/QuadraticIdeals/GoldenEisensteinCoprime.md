# Coprime Conjugate Factors of Cubic Lucas Blocks

## Abstract

The oriented Eisenstein factor of each cubic Lucas block is coprime to its conjugate.

**Theorem 1.1 (The oriented factor and its conjugate generate the unit ideal).**

$$\forall j \in \mathbb{N}, 1 \le j \implies \operatorname{IsCoprime}\left(\operatorname{IdealSpan}\left(\langle-2, \operatorname{goldenLucas}\left(3^{j}\right)-1\rangle\right), \operatorname{IdealSpan}\left(\operatorname{star}\left(\langle-2, \operatorname{goldenLucas}\left(3^{j}\right)-1\rangle\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/QuadraticIdeals/GoldenEisensteinCoprime.golden_eisenstein_conjugate_coprime` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For j at least one, let x be the Lucas number at index 3^j and let eta = -2 + (x - 1) omega in the Eisenstein order, where omega squared plus omega plus one is zero. The principal ideals of eta and its conjugate generate the unit ideal.

The Lucas residue x = 4 modulo 72 gives x = 4 + 72k for an integer k. The norm of eta is x squared plus three, while eta plus its conjugate equals -(x + 3). Since x squared plus three equals (x + 3)(x - 3) + 12 and x + 3 = 7 + 72k, explicit Bezout coefficients make these two integers coprime. Their image in the Eisenstein order supplies a Bezout identity for eta and its conjugate.

## References

- Truth anchor: `D5/S3/Factorization/QuadraticIdeals/GoldenEisensteinCoprime.golden_eisenstein_conjugate_coprime`
- Dependency: [D5/S1/Scale/GoldenCubicBlockCongruences](../../../S1/Scale/GoldenCubicBlockCongruences.md)
- Dependency: [D5/S3/Factorization/QuadraticIdeals/EisensteinOddQuotient](EisensteinOddQuotient.md)
